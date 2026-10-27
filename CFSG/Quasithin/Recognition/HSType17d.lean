module

public import CFSG.Quasithin.Recognition.HSType17c

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

section Fix

variable {G : Type*} [Group G]

theorem card_inf_centralizer_ge_four [Finite G] {A : Subgroup G}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : Nat.card A = 8) {t : G} (htt : t * t = 1)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) :
    4 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 := hA2 (a * b) (A.mul_mem ha hb)
    have h2 := hA2 a ha
    have h3 := hA2 b hb
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [inv_eq_of_mul_eq_one_left h3, inv_eq_of_mul_eq_one_left h2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  let ψ : ↥A →* ↥A :=
    { toFun := fun a => ⟨a * (t * a * t⁻¹), A.mul_mem a.2 (htA a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        have e := hAc b b.2 (t * a * t⁻¹) (htA a a.2)
        calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by
              group
          _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [e]
          _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group) }
  have hker : ∀ a : ↥A, ψ a = 1 ↔ (a : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    intro a
    constructor
    · intro h1
      have e : (a : G) * (t * a * t⁻¹) = 1 := congrArg Subtype.val h1
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have e2 : t * a * t⁻¹ = a := by
        rw [← mul_left_cancel_iff (a := (a : G)), e, hA2 a a.2]
      calc (a : G) * t = t * a * t⁻¹ * t := by rw [e2]
        _ = t * a := by group
    · intro hc
      apply Subtype.ext
      have hat : (a : G) * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp hc
      show (a : G) * (t * a * t⁻¹) = 1
      rw [← hat, mul_inv_cancel_right, hA2 a a.2]
  have hrange : ∀ a : ↥A, ((ψ a : ↥A) : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    intro a
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    show (a : G) * (t * a * t⁻¹) * t = t * ((a : G) * (t * a * t⁻¹))
    have e := hAc a a.2 (t * a * t⁻¹) (htA a a.2)
    rw [htinv] at e ⊢
    calc (a : G) * (t * a * t) * t = a * t * a * (t * t) := by simp only [mul_assoc]
      _ = a * t * a := by rw [htt, mul_one]
      _ = (t * t) * (a * t * a) := by rw [htt, one_mul]
      _ = t * (t * a * t * a) := by simp only [mul_assoc]
      _ = t * ((a : G) * (t * a * t)) := by rw [e]
  set C := A ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hkerC : Nat.card ψ.ker = Nat.card C := by
    refine Nat.card_congr ⟨fun a => ⟨a.1, a.1.2, (hker a.1).mp a.2⟩,
      fun c => ⟨⟨c, c.2.1⟩, (hker _).mpr c.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hrangeC : Nat.card ψ.range ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun b => ⟨(b.1 : G), b.1.2, by
      obtain ⟨a, ha⟩ := b.2
      rw [← ha]
      exact hrange a⟩) ?_
    intro b₁ b₂ hb
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hb))
  have hmul := ψ.ker.card_mul_index
  rw [Subgroup.index_ker, hA8, hkerC] at hmul
  have hle : 8 ≤ Nat.card C * Nat.card C := by
    rw [← hmul]
    exact Nat.mul_le_mul_left _ hrangeC
  have hdvd : Nat.card C ∣ 8 := by
    rw [← hA8]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hC8 : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases (Nat.card C) <;> omega

end Fix

abbrev t₅ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def InV5 (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ ∈ ({1, Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 2 3} :
    Finset (Equiv.Perm (Fin 5)))

instance : DecidablePred InV5 := fun σ => inferInstanceAs (Decidable (σ ∈ _))

theorem inV5_one : InV5 1 := by decide

theorem inV5_swap01 : InV5 (Equiv.swap 0 1) := by decide

theorem inV5_t5 : InV5 t₅ := by decide

theorem inV5_of_odd_invol : ∀ α : Equiv.Perm (Fin 5), α * α = 1 → Equiv.Perm.sign α = -1 →
    α * t₅ = t₅ * α → InV5 α := by
  decide +kernel

theorem inV5_mul_iff : ∀ σ τ : Equiv.Perm (Fin 5), σ * t₅ = t₅ * σ → τ * t₅ = t₅ * τ →
    (InV5 (σ * τ) ↔ (InV5 σ ↔ InV5 τ)) := by
  decide +kernel

theorem inV5_inv : ∀ σ : Equiv.Perm (Fin 5), InV5 σ → InV5 σ⁻¹ := by decide +kernel

theorem conj_swap01_of_not_inV5 : ∀ σ : Equiv.Perm (Fin 5), σ * t₅ = t₅ * σ → ¬ InV5 σ →
    σ * Equiv.swap 0 1 * σ⁻¹ = Equiv.swap 2 3 := by
  decide +kernel

theorem inV5_cases {σ : Equiv.Perm (Fin 5)} (h : InV5 σ) :
    σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 2 3 ∨ σ = t₅ := by
  simpa [InV5] using h

theorem swap23_eq : Equiv.swap (2 : Fin 5) 3 = Equiv.swap 0 1 * t₅ := by decide

theorem not_inV5_swap02 : ¬ InV5 (Equiv.swap 0 2 * Equiv.swap 1 3) := by decide

theorem swap02_comm_t5 : Equiv.swap 0 2 * Equiv.swap 1 3 * t₅ = t₅ * (Equiv.swap 0 2 *
    Equiv.swap 1 3) := by decide

theorem exists_norm_odd : ∀ α : Equiv.Perm (Fin 5), α * α = 1 → Equiv.Perm.sign α = -1 →
    α * t₅ = t₅ * α → ∃ ρ : Equiv.Perm (Fin 5), ρ * t₅ * ρ⁻¹ = t₅ ∧
      ρ * α * ρ⁻¹ = Equiv.swap 0 1 := by
  decide +kernel

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem sign_eq_one_of_mem_K [Finite G] (h : HSSetting z V) {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)}
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) {a : ↥(hsH z)} (haK : (a : G) ∈ hsK z) :
    Equiv.Perm.sign (φ a) = 1 := by
  have hm : φ a ∈ ((hsK z).subgroupOf (hsH z)).map φ := ⟨a, haK, rfl⟩
  rw [h.map_K_eq_alternating φ hker] at hm
  exact hm

theorem exists_quot_norm [Finite G] (h : HSSetting z V) {t s : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z)
    (hss : s * s = 1) (hst : s * t = t * s) :
    ∃ φ : ↥(hsH z) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = (hsQ z).subgroupOf (hsH z) ∧ φ ⟨t, htK.1⟩ = t₅ ∧
        φ ⟨s, hsmemH⟩ = Equiv.swap 0 1 := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hmem : ∀ a : ↥(hsH z), φ a = 1 ↔ (a : G) ∈ hsQ z := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set σ := φ ⟨t, htK.1⟩ with hσ
  set α := φ ⟨s, hsmemH⟩ with hα
  have hσ2 : σ * σ = 1 := by rw [hσ, ← map_mul]; exact (hmem _).mpr (by
    show t * t ∈ hsQ z; rw [htt]; exact (hsQ z).one_mem)
  have hσ1 : σ ≠ 1 := fun h1 => htQ ((hmem _).mp h1)
  have hσs : Equiv.Perm.sign σ = 1 := h.sign_eq_one_of_mem_K hker htK
  have hα2 : α * α = 1 := by rw [hα, ← map_mul]; exact (hmem _).mpr (by
    show s * s ∈ hsQ z; rw [hss]; exact (hsQ z).one_mem)
  have hαs : Equiv.Perm.sign α = -1 := h.sign_eq_neg_one_of_not_mem_K hker hsK
  have hασ : α * σ = σ * α := by
    rw [hα, hσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hst
  obtain ⟨ρ₁, -, hρ₁⟩ := alt_five_invol_conj σ hσs hσ2 hσ1
  set α' := ρ₁ * α * ρ₁⁻¹ with hα'
  have hα'2 : α' * α' = 1 := by
    rw [hα']
    calc ρ₁ * α * ρ₁⁻¹ * (ρ₁ * α * ρ₁⁻¹) = ρ₁ * (α * α) * ρ₁⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  have hα's : Equiv.Perm.sign α' = -1 := by
    rw [hα', map_mul, map_mul, map_inv, hαs]
    simp
  have hα't : α' * t₅ = t₅ * α' := by
    rw [hα', show t₅ = ρ₁ * σ * ρ₁⁻¹ from hρ₁.symm]
    calc ρ₁ * α * ρ₁⁻¹ * (ρ₁ * σ * ρ₁⁻¹) = ρ₁ * (α * σ) * ρ₁⁻¹ := by group
      _ = ρ₁ * (σ * α) * ρ₁⁻¹ := by rw [hασ]
      _ = ρ₁ * σ * ρ₁⁻¹ * (ρ₁ * α * ρ₁⁻¹) := by group
  obtain ⟨ρ₂, hρ₂t, hρ₂α⟩ := exists_norm_odd α' hα'2 hα's hα't
  set ρ := ρ₂ * ρ₁ with hρ
  refine ⟨(MulAut.conj ρ).toMonoidHom.comp φ, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj ρ).surjective.comp hφ
  · rw [MonoidHom.ker_comp_of_injective φ _ (MulAut.conj ρ).injective, hker]
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [← hσ, hρ]
    calc ρ₂ * ρ₁ * σ * (ρ₂ * ρ₁)⁻¹ = ρ₂ * (ρ₁ * σ * ρ₁⁻¹) * ρ₂⁻¹ := by group
      _ = t₅ := by rw [hρ₁, hρ₂t]
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [← hα, hρ]
    calc ρ₂ * ρ₁ * α * (ρ₂ * ρ₁)⁻¹ = ρ₂ * α' * ρ₂⁻¹ := by rw [hα']; group
      _ = Equiv.swap 0 1 := hρ₂α

theorem exists_mem_T_of_comm [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)}
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) (hφt : φ ⟨t, htK.1⟩ = t₅)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ * t₅ = t₅ * σ) :
    ∃ y : G, ∃ hy : y ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G), φ ⟨y, hy.1⟩ = σ := by
  set T := hsH z ⊓ Subgroup.centralizer ({t} : Set G) with hT
  let φT : ↥T →* Equiv.Perm (Fin 5) := φ.comp (Subgroup.inclusion inf_le_left)
  have hφT : ∀ y : ↥T, φT y = φ ⟨(y : G), y.2.1⟩ := fun _ => rfl
  have hmem : ∀ a : ↥(hsH z), φ a = 1 ↔ (a : G) ∈ hsQ z := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hkercard : Nat.card φT.ker = 8 := by
    obtain ⟨v, hvQ, hvt⟩ := h.exists_v_of_invol_K htK htQ htt
    rw [← h.card_centralizer_invol_K htK htQ htt hvQ hvt]
    refine Nat.card_congr ⟨fun y => ⟨(y : G), (hmem _).mp y.2, y.1.2.2⟩,
      fun q => ⟨⟨q, h.Q_le_H q.2.1, q.2.2⟩, (hmem _).mpr q.2.1⟩, fun _ => rfl, fun _ => rfl⟩
  have hrange : φT.range ≤ Subgroup.centralizer ({t₅} : Set (Equiv.Perm (Fin 5))) := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [hφT, ← hφt, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2.2)
  have hmul := φT.ker.card_mul_index
  rw [Subgroup.index_ker, hkercard, h.card_centralizer_H_of_invol_K htK htQ htt] at hmul
  have h8 : Nat.card ↥(Subgroup.centralizer ({t₅} : Set (Equiv.Perm (Fin 5)))) = 8 :=
    card_centralizer_perm_of_alt (by decide) (by decide) (by decide)
  have heq : φT.range = Subgroup.centralizer ({t₅} : Set (Equiv.Perm (Fin 5))) :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [h8]; omega)
  have hσmem : σ ∈ φT.range := by
    rw [heq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hσ
  obtain ⟨y, hy⟩ := hσmem
  exact ⟨y, y.2, hy⟩

theorem inv_of_mem_CQt [Finite G] (h : HSSetting z V) {t s : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z)
    (hss : s * s = 1) (hst : s * t = t * s) {q : G} (hq : q ∈ hsQ z)
    (hqt : q * t = t * q) : s * q * s⁻¹ = q⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hsZ : ∀ c ∈ hsZQ z, s * c * s⁻¹ = c⁻¹ := by
    intro c hc
    rcases h.mem_K_or_inverts hsmemH with hK | hinv
    · exact absurd hK hsK
    · exact hinv c hc
  set A := hsQ z ⊓ Subgroup.centralizer ({s} : Set G) with hA
  have hA8 : Nat.card A = 8 := h.card_centralizer_invol hsmemH hsK hss
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha =>
    h.mul_self_of_mem_centralizer_invol hsmemH hsK hss ha
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := by
    intro a ha
    refine ⟨conj_mem_Q htK.1 ha.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have has : a * s = s * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have hts : t⁻¹ * s = s * t⁻¹ := by
      calc t⁻¹ * s = t⁻¹ * (s * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * s) * t⁻¹ := by rw [hst]
        _ = s * t⁻¹ := by group
    calc t * a * t⁻¹ * s = t * a * (t⁻¹ * s) := by group
      _ = t * a * (s * t⁻¹) := by rw [hts]
      _ = t * (a * s) * t⁻¹ := by group
      _ = t * (s * a) * t⁻¹ := by rw [has]
      _ = (t * s) * a * t⁻¹ := by group
      _ = (s * t) * a * t⁻¹ := by rw [hst]
      _ = s * (t * a * t⁻¹) := by group
  have hW := card_inf_centralizer_ge_four hA2 hA8 htt htA
  obtain ⟨b, hbW, hbZ⟩ : ∃ b ∈ A ⊓ Subgroup.centralizer ({t} : Set G), b ∉ hsZQ z := by
    by_contra hne
    push Not at hne
    have hle : A ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.zpowers z := by
      intro b hb
      have hbZ := hne b hb
      have hb2 := hA2 b hb.1
      by_cases hb1 : b = 1
      · rw [hb1]; exact Subgroup.one_mem _
      · rw [h.eq_z_of_mem_ZQ hbZ hb2 hb1]; exact Subgroup.mem_zpowers z
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, h.orderOf_z] at this
    omega
  have hbQ : b ∈ hsQ z := hbW.1.1
  have hbs : b * s = s * b := Subgroup.mem_centralizer_singleton_iff.mp hbW.1.2
  have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hbW.2
  have hb2 : b * b = 1 := hA2 b hbW.1
  set CQ := hsQ z ⊓ Subgroup.centralizer ({t} : Set G) with hCQ
  have hZC : hsZQ z ≤ CQ := fun c hc =>
    ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp htK.2 c hc)⟩
  obtain ⟨v, hvQ, hvt⟩ := h.exists_v_of_invol_K htK htQ htt
  have hCQ8 : Nat.card CQ = 8 := h.card_centralizer_invol_K htK htQ htt hvQ hvt
  have hidx : ((hsZQ z).subgroupOf CQ).index = 2 := by
    have h1 := ((hsZQ z).subgroupOf CQ).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, h.card_ZQ, hCQ8] at h1
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hbC : b ∈ CQ := ⟨hbQ, hbW.2⟩
  have hqC : q ∈ CQ := ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqt⟩
  have hdec : q ∈ hsZQ z ∨ q * b⁻¹ ∈ hsZQ z := by
    by_cases hqZ : q ∈ hsZQ z
    · exact Or.inl hqZ
    · right
      have hq' := ha ⟨q, hqC⟩
      have hb' := ha ⟨b, hbC⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hq' hb'
      have hqa : q * (a : G) ∈ hsZQ z := by
        rcases hq' with ⟨h1, -⟩ | ⟨h2, -⟩
        · exact h1
        · exact absurd h2 hqZ
      have hba : b * (a : G) ∈ hsZQ z := by
        rcases hb' with ⟨h1, -⟩ | ⟨h2, -⟩
        · exact h1
        · exact absurd h2 hbZ
      have := (hsZQ z).mul_mem hqa ((hsZQ z).inv_mem hba)
      rwa [show q * (a : G) * (b * (a : G))⁻¹ = q * b⁻¹ by group] at this
  rcases hdec with hqZ | hqb
  · exact hsZ q hqZ
  · obtain ⟨c, hc⟩ : ∃ c, c = q * b⁻¹ := ⟨_, rfl⟩
    rw [← hc] at hqb
    have hqcb : q = c * b := by rw [hc]; group
    have hcQ : ∀ x ∈ hsQ z, c * x = x * c := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hqb.2 x hx).symm
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
    rw [hqcb]
    calc s * (c * b) * s⁻¹ = (s * c * s⁻¹) * (s * b * s⁻¹) := by group
      _ = c⁻¹ * b := by
          rw [hsZ c hqb, show s * b * s⁻¹ = b by rw [← hbs]; group]
      _ = c⁻¹ * (b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hcQ b hbQ]
      _ = b * c⁻¹ := by group
      _ = (c * b)⁻¹ := by rw [mul_inv_rev, hbinv]

end HSSetting

theorem inV5_mul : ∀ σ τ : Equiv.Perm (Fin 5), InV5 σ → InV5 τ → InV5 (σ * τ) := by
  decide +kernel

@[expose] def sPrime {G : Type} [Group G] {z : G} (φ : ↥(hsH z) →* Equiv.Perm (Fin 5)) (t : G) :
    Subgroup G where
  carrier := {y | y ∈ Subgroup.centralizer ({t} : Set G) ∧ ∃ hy : y ∈ hsH z, InV5 (φ ⟨y, hy⟩)}
  mul_mem' := by
    rintro a b ⟨hat, haH, ha⟩ ⟨hbt, hbH, hb⟩
    refine ⟨Subgroup.mul_mem _ hat hbt, Subgroup.mul_mem _ haH hbH, ?_⟩
    have e : (⟨a * b, Subgroup.mul_mem _ haH hbH⟩ : ↥(hsH z)) = ⟨a, haH⟩ * ⟨b, hbH⟩ := rfl
    rw [e, map_mul]
    exact inV5_mul _ _ ha hb
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, by
    have e : (⟨1, Subgroup.one_mem _⟩ : ↥(hsH z)) = 1 := rfl
    rw [e, map_one]; exact inV5_one⟩
  inv_mem' := by
    rintro a ⟨hat, haH, ha⟩
    refine ⟨Subgroup.inv_mem _ hat, Subgroup.inv_mem _ haH, ?_⟩
    have e : (⟨a⁻¹, Subgroup.inv_mem _ haH⟩ : ↥(hsH z)) = (⟨a, haH⟩)⁻¹ := rfl
    rw [e, map_inv]
    exact inV5_inv _ ha

theorem mem_sPrime {G : Type} [Group G] {z : G} {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} {t y : G} :
    y ∈ sPrime φ t ↔
      y ∈ Subgroup.centralizer ({t} : Set G) ∧ ∃ hy : y ∈ hsH z, InV5 (φ ⟨y, hy⟩) :=
  Iff.rfl

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

section SPrime

variable (h : HSSetting z V) {t s : G} (htK : t ∈ hsK z) (htQ : t ∉ hsQ z)
  (htt : t * t = 1) {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)}
  (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) (hφt : φ ⟨t, htK.1⟩ = t₅)

include htK hφt in
theorem π_comm_of_mem_T {y : G} (hyH : y ∈ hsH z) (hyt : y * t = t * y) :
    φ ⟨y, hyH⟩ * t₅ = t₅ * φ ⟨y, hyH⟩ := by
  rw [← hφt, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hyt

theorem sPrime_le_T : sPrime φ t ≤ hsH z ⊓ Subgroup.centralizer ({t} : Set G) := by
  rintro y ⟨hyt, hyH, -⟩
  exact ⟨hyH, hyt⟩

include htK hφt in
theorem t_mem_sPrime : t ∈ sPrime φ t :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, htK.1, by rw [hφt]; exact inV5_t5⟩

include htK hφt in
theorem mem_sPrime_mul_iff {a b : G} (ha : a ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G))
    (hb : b ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G)) :
    a * b ∈ sPrime φ t ↔ (a ∈ sPrime φ t ↔ b ∈ sPrime φ t) := by
  have hat := π_comm_of_mem_T htK hφt ha.1 (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
  have hbt := π_comm_of_mem_T htK hφt hb.1 (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
  have key := inV5_mul_iff _ _ hat hbt
  have e : (⟨a * b, Subgroup.mul_mem _ ha.1 hb.1⟩ : ↥(hsH z)) = ⟨a, ha.1⟩ * ⟨b, hb.1⟩ := rfl
  simp only [mem_sPrime]
  constructor
  · rintro ⟨-, hH, hV⟩
    rw [show (⟨a * b, hH⟩ : ↥(hsH z)) = ⟨a, ha.1⟩ * ⟨b, hb.1⟩ from rfl, map_mul] at hV
    have := key.mp hV
    exact ⟨fun ⟨_, _, h1⟩ => ⟨hb.2, hb.1, this.mp h1⟩,
      fun ⟨_, _, h1⟩ => ⟨ha.2, ha.1, this.mpr h1⟩⟩
  · intro hiff
    refine ⟨Subgroup.mul_mem _ ha.2 hb.2, Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    rw [e, map_mul]
    refine key.mpr ⟨fun h1 => ?_, fun h1 => ?_⟩
    · exact (hiff.mp ⟨ha.2, ha.1, h1⟩).2.2
    · exact (hiff.mpr ⟨hb.2, hb.1, h1⟩).2.2

include h htK hker hφt in
theorem mem_sPrime_of_isConj [Finite G] {u : G}
    (hu : u ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G)) (huz : IsConj z u) : u ∈ sPrime φ t := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp huz
  refine ⟨hu.2, hu.1, ?_⟩
  by_cases huK : g * z * g⁻¹ ∈ hsK z
  · have huQ := h.mem_Q_of_conj_mem_K huK
    have : φ ⟨g * z * g⁻¹, hu.1⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact huQ
    rw [this]; exact inV5_one
  · have hs := h.sign_eq_neg_one_of_not_mem_K hker (a := ⟨_, hu.1⟩) huK
    have h2 : φ ⟨g * z * g⁻¹, hu.1⟩ * φ ⟨g * z * g⁻¹, hu.1⟩ = 1 := by
      rw [← map_mul]
      have : (⟨g * z * g⁻¹, hu.1⟩ : ↥(hsH z)) * ⟨g * z * g⁻¹, hu.1⟩ = 1 :=
        Subtype.ext (by
          show g * z * g⁻¹ * (g * z * g⁻¹) = 1
          calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
            _ = 1 := by rw [h.z_mul_z]; group)
      rw [this, map_one]
    exact inV5_of_odd_invol _ h2 hs
      (π_comm_of_mem_T htK hφt hu.1 (Subgroup.mem_centralizer_singleton_iff.mp hu.2))

include h htQ htt hker hφt in
theorem sq_mem_sPrime [Finite G] (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z) (hss : s * s = 1)
    (hst : s * t = t * s) (hφs : φ ⟨s, hsmemH⟩ = Equiv.swap 0 1) {y : G}
    (hy : y ∈ sPrime φ t) : y * y = 1 ∨ y * y = z := by
  obtain ⟨hyt, hyH, hyV⟩ := hy
  have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyt
  have hmem : ∀ a : ↥(hsH z), φ a = 1 ↔ (a : G) ∈ hsQ z := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hinvq : ∀ q : G, q ∈ hsQ z → q * t = t * q → s * q * s⁻¹ = q⁻¹ := fun q hq hqt =>
    h.inv_of_mem_CQt htK htQ htt hsmemH hsK hss hst hq hqt
  rcases inV5_cases hyV with h1 | h1 | h1 | h1
  · exact h.mul_self_eq_one_or_z ((hmem _).mp h1)
  ·
    have hq : s⁻¹ * y ∈ hsQ z := by
      have : φ ⟨s⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _ hsmemH) hyH⟩ = 1 := by
        rw [show (⟨s⁻¹ * y, _⟩ : ↥(hsH z)) = (⟨s, hsmemH⟩)⁻¹ * ⟨y, hyH⟩ from rfl, map_mul,
          map_inv, hφs, h1, inv_mul_cancel]
      exact (hmem _).mp this
    have hqt : s⁻¹ * y * t = t * (s⁻¹ * y) := by
      rw [hsinv, mul_assoc, hyt', ← mul_assoc, hst, mul_assoc]
    have e := hinvq _ hq hqt
    left
    calc y * y = s * (s⁻¹ * y) * (s * (s⁻¹ * y)) := by group
      _ = (s * (s⁻¹ * y) * s⁻¹) * (s * s) * (s⁻¹ * y) := by group
      _ = 1 := by rw [e, hss, mul_one, inv_mul_cancel]
  ·
    have hq : (s * t)⁻¹ * y ∈ hsQ z := by
      have : φ ⟨(s * t)⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _
          (Subgroup.mul_mem _ hsmemH htK.1)) hyH⟩ = 1 := by
        rw [show (⟨(s * t)⁻¹ * y, _⟩ : ↥(hsH z)) =
            (⟨s, hsmemH⟩ * ⟨t, htK.1⟩)⁻¹ * ⟨y, hyH⟩ from rfl, map_mul, map_inv, map_mul, hφs,
          hφt, h1, swap23_eq, inv_mul_cancel]
      exact (hmem _).mp this
    set q := (s * t)⁻¹ * y with hqdef
    have hqt : q * t = t * q := by
      rw [hqdef, mul_inv_rev, htinv, hsinv]
      calc t * s * y * t = t * s * (y * t) := by group
        _ = t * s * (t * y) := by rw [hyt']
        _ = t * (s * t) * y := by group
        _ = t * (t * s) * y := by rw [hst]
        _ = t * (t * s * y) := by group
    have e := hinvq _ hq hqt
    have hy' : y = s * t * q := by rw [hqdef]; group
    left
    rw [hy']
    have hsq : s * q = q⁻¹ * s := by
      calc s * q = s * q * s⁻¹ * s := by group
        _ = q⁻¹ * s := by rw [e]
    calc s * t * q * (s * t * q) = s * (t * q) * s * (t * q) := by group
      _ = s * (q * t) * s * (q * t) := by rw [hqt]
      _ = (s * q) * (t * s) * q * t := by group
      _ = (q⁻¹ * s) * (s * t) * q * t := by rw [hsq, hst]
      _ = q⁻¹ * (s * s) * t * q * t := by group
      _ = q⁻¹ * (t * q) * t := by rw [hss]; group
      _ = q⁻¹ * (q * t) * t := by rw [hqt]
      _ = 1 := by rw [← mul_assoc, inv_mul_cancel, one_mul, htt]
  ·
    have hq : t⁻¹ * y ∈ hsQ z := by
      have : φ ⟨t⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _ htK.1) hyH⟩ = 1 := by
        rw [show (⟨t⁻¹ * y, _⟩ : ↥(hsH z)) = (⟨t, htK.1⟩)⁻¹ * ⟨y, hyH⟩ from rfl, map_mul,
          map_inv, hφt, h1, inv_mul_cancel]
      exact (hmem _).mp this
    have hqt : t⁻¹ * y * t = t * (t⁻¹ * y) := by
      rw [mul_assoc, hyt']; group
    rcases h.mul_self_eq_one_or_z hq with h2 | h2
    · left
      calc y * y = t * (t⁻¹ * y) * (t * (t⁻¹ * y)) := by group
        _ = (t * t) * ((t⁻¹ * y) * (t⁻¹ * y)) := by
            rw [show t * (t⁻¹ * y) * (t * (t⁻¹ * y)) = t * ((t⁻¹ * y) * t) * (t⁻¹ * y) by group,
              hqt]; group
        _ = 1 := by rw [htt, h2, one_mul]
    · right
      calc y * y = t * (t⁻¹ * y) * (t * (t⁻¹ * y)) := by group
        _ = (t * t) * ((t⁻¹ * y) * (t⁻¹ * y)) := by
            rw [show t * (t⁻¹ * y) * (t * (t⁻¹ * y)) = t * ((t⁻¹ * y) * t) * (t⁻¹ * y) by group,
              hqt]; group
        _ = z := by rw [htt, h2, one_mul]

end SPrime

end HSSetting

end CFSG.Quasithin.HSType
