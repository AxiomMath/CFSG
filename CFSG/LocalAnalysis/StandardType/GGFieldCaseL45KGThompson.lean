module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGPowMap
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem ggL45_mem_centralizer_singleton_iff' (b v : G) :
    v ∈ Subgroup.centralizer ({b} : Set G) ↔ b * v = v * b := by
  rw [Subgroup.mem_centralizer_iff]
  simp

theorem thompson_eq_of_cent_bound [Finite G] {p : ℕ} [Fact p.Prime] {U U₁ : Subgroup G} {g : G}
    (hU₁U : U₁ ≤ U) (hUN : U ≤ Subgroup.normalizer (U₁ : Set G)) (hUp : IsPGroup p U)
    (hab : IsMulCommutative U₁) (hgU : g ∈ U) (hcyc : U ≤ Subgroup.zpowers g ⊔ U₁)
    (hbig : ∀ y ∈ U, y ∉ U₁ → y ^ p ∈ U₁ →
      Nat.card (U₁ ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) * p ^ 2 ≤ Nat.card U₁) :
    ∀ A ∈ thompsonAbelianSubgroups U, A = U₁ := by
  have hp := (Fact.out : p.Prime)
  have hcomm : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  intro A hA
  obtain ⟨hAU, hAab, hAmax⟩ := hA
  have hU₁A : Nat.card U₁ ≤ Nat.card A := hAmax U₁ hU₁U hab
  by_contra hne
  have hAU₁ : ¬ A ≤ U₁ := fun h => hne (Subgroup.eq_of_le_of_card_ge h hU₁A)
  obtain ⟨a, haA, j, hAle, haj1, hajU₁⟩ :=
    exists_gen_mod_of_cyclic hU₁U hUN hUp hgU hcyc hAU hAU₁
  have hyU : a ^ p ^ j ∈ U := U.pow_mem (hAU haA) _
  have hyp : (a ^ p ^ j) ^ p ∈ U₁ := by rw [← pow_mul, ← pow_succ]; exact haj1
  have hb := hbig _ hyU hajU₁ hyp
  have hU₁pos : 0 < Nat.card U₁ := Nat.card_pos
  have h2 := hp.two_le
  have hajC : a ^ p ^ j ∉ Subgroup.centralizer (U₁ : Set G) := by
    intro h
    have hle : Nat.card U₁ ≤
        Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) :=
      Subgroup.card_le_of_le fun v hv =>
        ⟨hv, (ggL45_mem_centralizer_singleton_iff' _ v).mpr
          (Subgroup.mem_centralizer_iff.mp h v hv).symm⟩
    have : Nat.card U₁ * p ^ 2 ≤ Nat.card U₁ := (Nat.mul_le_mul_right _ hle).trans hb
    have h4 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    have := Nat.mul_lt_mul_of_pos_left h4 hU₁pos
    omega
  have hU₁C : U₁ ≤ Subgroup.centralizer (U₁ : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hcomm w hw v hv
  have haN : a ∈ Subgroup.normalizer (U₁ : Set G) := hUN (hAU haA)
  have hchain := card_inf_centralizer_mul_pow_le hab (hUp.to_le hU₁U) haN (hU₁C haj1) j hajC
  have hAC : A ⊓ U₁ ≤ U₁ ⊓ Subgroup.centralizer ({a} : Set G) := fun v hv =>
    ⟨hv.2, (ggL45_mem_centralizer_singleton_iff' a v).mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨a, haA⟩ ⟨v, hv.1⟩))⟩
  have hcount := card_le_card_inf_mul_of_le_sup haA haN hAle (pow_pos hp.pos _) haj1
  have hAC' := Subgroup.card_le_of_le hAC
  have key : Nat.card A ≤
      Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) * p := by
    calc Nat.card A ≤ Nat.card (A ⊓ U₁ : Subgroup G) * p ^ (j + 1) := hcount
      _ ≤ Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ (j + 1) :=
          Nat.mul_le_mul_right _ hAC'
      _ = Nat.card (U₁ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p ^ j * p := by
          rw [pow_succ, mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_right _ hchain
  have hApos : 0 < Nat.card A := Nat.card_pos
  have : Nat.card A * p ≤ Nat.card U₁ := by
    calc Nat.card A * p ≤
        Nat.card (U₁ ⊓ Subgroup.centralizer ({a ^ p ^ j} : Set G) : Subgroup G) * p * p :=
          Nat.mul_le_mul_right _ key
      _ = _ * p ^ 2 := by ring
      _ ≤ _ := hb
  have := Nat.mul_le_mul_left (Nat.card A) h2
  omega

theorem ggL45_sq_le_card_of_indep {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {b₁ b₂ : M} (hc : Commute b₁ b₂) (h₁ : b₁ ^ p = 1) (h₂ : b₂ ^ p = 1)
    (hind : ∀ i j : ℕ, b₁ ^ i * b₂ ^ j = 1 → p ∣ i ∧ p ∣ j) {S : Subgroup M}
    (hb₁ : b₁ ∈ S) (hb₂ : b₂ ∈ S) : p ^ 2 ≤ Nat.card S := by
  let f : Fin p × Fin p → S := fun ij =>
    ⟨b₁ ^ (ij.1 : ℕ) * b₂ ^ (ij.2 : ℕ), S.mul_mem (S.pow_mem hb₁ _) (S.pow_mem hb₂ _)⟩
  have key : ∀ i i' : ℕ, i < p → i' < p → p ∣ i + (p - i') → i = i' := by
    intro i i' hi hi' hd
    have hd' : (p : ℤ) ∣ ((i : ℤ) - i') := by
      have : ((i + (p - i') : ℕ) : ℤ) = ((i : ℤ) - i') + p := by
        rw [Nat.cast_add, Nat.cast_sub hi'.le]; ring
      have h1 := Int.natCast_dvd_natCast.mpr hd
      rw [this] at h1
      exact (dvd_add_left (dvd_refl (p : ℤ))).mp h1
    have h0 := Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
    omega
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : b₁ ^ (i : ℕ) * b₂ ^ (j : ℕ) = b₁ ^ (i' : ℕ) * b₂ ^ (j' : ℕ) :=
      congrArg Subtype.val h
    have hrel : b₁ ^ ((i : ℕ) + (p - i')) * b₂ ^ ((j : ℕ) + (p - j')) = 1 := by
      have e1 : b₁ ^ ((i : ℕ) + (p - i')) * b₂ ^ ((j : ℕ) + (p - j')) =
          (b₁ ^ (i : ℕ) * b₂ ^ (j : ℕ)) * (b₁ ^ (p - i') * b₂ ^ (p - j')) := by
        rw [pow_add, pow_add, mul_assoc, mul_assoc, ← mul_assoc (b₁ ^ (p - (i' : ℕ))),
          ((hc.pow_pow (p - (i' : ℕ)) (j : ℕ)).eq), mul_assoc]
      rw [e1, h']
      have e2 : (b₁ ^ (i' : ℕ) * b₂ ^ (j' : ℕ)) * (b₁ ^ (p - i') * b₂ ^ (p - j')) =
          b₁ ^ ((i' : ℕ) + (p - i')) * b₂ ^ ((j' : ℕ) + (p - j')) := by
        rw [pow_add, pow_add, mul_assoc, mul_assoc, ← mul_assoc (b₂ ^ (j' : ℕ)),
          ((hc.pow_pow (p - (i' : ℕ)) (j' : ℕ)).eq.symm), mul_assoc]
      rw [e2, Nat.add_sub_cancel' i'.2.le, Nat.add_sub_cancel' j'.2.le, h₁, h₂, mul_one]
    obtain ⟨hdi, hdj⟩ := hind _ _ hrel
    have := key i i' i.2 i'.2 hdi
    have := key j j' j.2 j'.2 hdj
    ext <;> simp_all
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fin] at this
  rw [pow_two]
  exact this

end General

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.kg_zind
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) (hxU₁ : x ∉ U₁) {s : ℕ} (hs : 2 ≤ s)
    (hP2m : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      h * t = t * h ∧ GGL45IsPElt p (h * t))
    (hP2e : ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → h ^ p ^ s = 1)
    (hP4 : ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e = e * γ) →
      ¬ GGL45InducesIn θ I γ → GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
        γ h = h ^ (1 + p ^ (s - 1) * k'))
    {a₁ a₂ : K} (ha₁ : GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a₁)
    (ha₂ : GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a₂)
    (hind : ∀ i j : ℕ, (a₁ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₁)⁻¹) ^ i *
        (a₂ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₂)⁻¹) ^ j = 1 →
        p ∣ i ∧ p ∣ j) :
    ∀ m : ℕ, ¬ p ∣ m → ∀ i j : ℕ,
      ((((a₁ : G) ^ p ^ (s - 1)) ^ m) ^ i) * ((((a₂ : G) ^ p ^ (s - 1)) ^ m) ^ j) = 1 →
      p ∣ i ∧ p ∣ j := by
  have hp : p.Prime := hcfg.prime
  have hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t) := fun h t hh ht => (hP2m h t hh ht).2
  have haU₁ : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a → (a : G) ∈ U₁ := fun a ha =>
    hcfg.kg_S_mem θ hinn hiff hmul ha
  have haUK : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a → (a : G) ∈ U ⊓ K := fun a ha =>
    ⟨hcfg.part_le (haU₁ a ha), a.2⟩
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  obtain ⟨kx, hkx, hxact⟩ := hcfg.kg_powmap θ hiff hP4 (U.inv_mem hxU)
    (fun h => hxU₁ (by simpa using U₁.inv_mem h))
    (by rw [inv_pow, hcfg.x_pow, inv_one]; exact U₁.one_mem)
  have hzp : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a →
      ((a : G) ^ p ^ (s - 1)) ^ p = 1 := by
    intro a ha
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]
    simpa using congrArg Subtype.val (hP2e a ha)
  have hzc : Commute ((a₁ : G) ^ p ^ (s - 1)) ((a₂ : G) ^ p ^ (s - 1)) :=
    ((show Commute (a₁ : G) a₂ from congrArg Subtype.val (hP2m a₁ a₂ ha₁ ha₂).1).pow_pow _ _)
  have hbx : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a →
      ((a * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a)⁻¹ : K) : G) =
        (((a : G) ^ p ^ (s - 1)) ^ kx)⁻¹ := by
    intro a ha
    rw [coe_comm_psi hcfg.kg_xN]
    have h1 := hxact a (haUK a ha)
    simp only [inv_inv] at h1
    have e : (a : G) * x * (a : G)⁻¹ * x⁻¹ = (a : G) * (x * a * x⁻¹)⁻¹ := by group
    rw [e, h1, pow_add, pow_one, ← pow_mul]
    group
  have hinvp : ∀ w : G, w ^ p = 1 → (w⁻¹) ^ (p - 1) = w := by
    intro w hw
    have : (w⁻¹) ^ (p - 1) * w⁻¹ = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, inv_pow, hw, inv_one]
    calc (w⁻¹) ^ (p - 1) = (w⁻¹) ^ (p - 1) * w⁻¹ * w := by group
      _ = w := by rw [this, one_mul]
  have hw : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a →
      (((a : G) ^ p ^ (s - 1)) ^ kx) ^ p = 1 :=
    fun a ha => by rw [← pow_mul, mul_comm, pow_mul, hzp a ha, one_pow]
  have epow : ∀ (c : G) (m n : ℕ), (c ^ kx) ^ (m * n) = ((c ^ m) ^ n) ^ kx := by
    intro c m n
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have h2 := hp.two_le
  have hp1 : ¬ p ∣ p - 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  intro m hm i j hij
  have hrel := hind ((p - 1) * (m * i)) ((p - 1) * (m * j)) (Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, hbx a₁ ha₁,
      hbx a₂ ha₂, pow_mul _ (p - 1) (m * i), pow_mul _ (p - 1) (m * j), hinvp _ (hw a₁ ha₁),
      hinvp _ (hw a₂ ha₂), epow, epow,
      ← (((hzc.pow_pow m m).pow_pow i j).mul_pow kx), hij, one_pow]))
  have hpd : ∀ n : ℕ, p ∣ (p - 1) * (m * n) → p ∣ n := by
    intro n hn
    rcases (Nat.Prime.dvd_mul hp).mp hn with h | h
    · exact absurd h hp1
    · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · exact absurd h' hm
      · exact h'
  exact ⟨hpd i hrel.1, hpd j hrel.2⟩

theorem GGL45Config.kg_cent_bound
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) (hxU₁ : x ∉ U₁) {s : ℕ} (hs : 2 ≤ s)
    (hP2m : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      h * t = t * h ∧ GGL45IsPElt p (h * t))
    (hP2e : ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h → h ^ p ^ s = 1)
    (hP3 : ∃ a₁ a₂ : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a₁ ∧
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a₂ ∧
      (a₁ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₁)⁻¹) ^ p = 1 ∧
      (a₂ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₂)⁻¹) ^ p = 1 ∧
      a₁ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₁)⁻¹ ∉ Subgroup.center K ∧
      ∀ i j : ℕ, (a₁ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₁)⁻¹) ^ i *
        (a₂ * ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ a₂)⁻¹) ^ j = 1 →
        p ∣ i ∧ p ∣ j)
    (hP4 : ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e = e * γ) →
      ¬ GGL45InducesIn θ I γ → GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
        γ h = h ^ (1 + p ^ (s - 1) * k'))
    (hab : IsMulCommutative U₁) :
    ∀ w ∈ U, w ∉ U₁ → w ^ p ∈ U₁ →
      Nat.card (U₁ ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) * p ^ 2 ≤
        Nat.card U₁ := by
  have hp : p.Prime := hcfg.prime
  have hcomm : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨a₁, a₂, ha₁, ha₂, -, -, -, hind⟩ := hP3
  have hzind := hcfg.kg_zind θ hinn hiff hxU₁ hs hP2m hP2e hP4 ha₁ ha₂ hind
  have hmul : ∀ h t : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) h →
      GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) t →
      GGL45IsPElt p (h * t) := fun h t hh ht => (hP2m h t hh ht).2
  have haU₁ : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a → (a : G) ∈ U₁ := fun a ha =>
    hcfg.kg_S_mem θ hinn hiff hmul ha
  have haUK : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a → (a : G) ∈ U ⊓ K := fun a ha =>
    ⟨hcfg.part_le (haU₁ a ha), a.2⟩
  have hzp : ∀ a : K, GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a →
      ((a : G) ^ p ^ (s - 1)) ^ p = 1 := by
    intro a ha
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]
    simpa using congrArg Subtype.val (hP2e a ha)
  have hzc : Commute ((a₁ : G) ^ p ^ (s - 1)) ((a₂ : G) ^ p ^ (s - 1)) :=
    ((show Commute (a₁ : G) a₂ from congrArg Subtype.val (hP2m a₁ a₂ ha₁ ha₂).1).pow_pow _ _)
  intro w hwU hwU₁ hwp
  obtain ⟨k', hk', hwact⟩ := hcfg.kg_powmap θ hiff hP4 hwU hwU₁ hwp
  have hconj : ∀ u ∈ U₁, w⁻¹ * u * w ∈ U₁ := fun u hu => by
    simpa using hcfg.conj_mem_part (U.inv_mem hwU) hu
  let f : U₁ →* U₁ :=
    { toFun := fun u => ⟨(u : G)⁻¹ * (w⁻¹ * u * w), U₁.mul_mem (U₁.inv_mem u.2) (hconj u u.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by
        show ((u : G) * v)⁻¹ * (w⁻¹ * (u * v) * w) =
          (u : G)⁻¹ * (w⁻¹ * u * w) * ((v : G)⁻¹ * (w⁻¹ * v * w))
        have hc := hcomm (v : G)⁻¹ (U₁.inv_mem v.2) ((u : G)⁻¹ * (w⁻¹ * u * w))
          (U₁.mul_mem (U₁.inv_mem u.2) (hconj u u.2))
        calc ((u : G) * v)⁻¹ * (w⁻¹ * (u * v) * w)
            = (v : G)⁻¹ * ((u : G)⁻¹ * (w⁻¹ * u * w)) * (w⁻¹ * v * w) := by group
          _ = (u : G)⁻¹ * (w⁻¹ * u * w) * (v : G)⁻¹ * (w⁻¹ * v * w) := by rw [hc]
          _ = _ := by group) }
  have hker : f.ker.map U₁.subtype = U₁ ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h1 : (u : G)⁻¹ * (w⁻¹ * u * w) = 1 := congrArg Subtype.val hu
      refine ⟨u.2, (ggL45_mem_centralizer_singleton_iff' w _).mpr ?_⟩
      have h2 : w⁻¹ * u * w = u := by
        calc w⁻¹ * u * w = (u : G) * ((u : G)⁻¹ * (w⁻¹ * u * w)) := by group
          _ = u := by rw [h1, mul_one]
      calc w * u = w * (w⁻¹ * u * w) := by rw [h2]
        _ = u * w := by group
    · rintro ⟨hg, hgc⟩
      have h1 : w * g = g * w := (ggL45_mem_centralizer_singleton_iff' w g).mp hgc
      refine ⟨⟨g, hg⟩, Subtype.ext ?_, rfl⟩
      show g⁻¹ * (w⁻¹ * g * w) = 1
      rw [mul_assoc, ← h1]
      group
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [← Subgroup.card_map_of_injective U₁.subtype_injective, hker] at hcard
  have hfa : ∀ a : K, ∀ ha : GGL45InS p (ggL45KgE K _ hcfg.kg_B1N) a,
      ((f ⟨a, haU₁ a ha⟩ : U₁) : G) = ((a : G) ^ p ^ (s - 1)) ^ k' := by
    intro a ha
    show (a : G)⁻¹ * (w⁻¹ * a * w) = _
    rw [hwact a (haUK a ha), pow_add, pow_one, ← pow_mul]
    group
  have hrange : p ^ 2 ≤ Nat.card f.range := by
    refine ggL45_sq_le_card_of_indep hp (b₁ := f ⟨a₁, haU₁ a₁ ha₁⟩)
      (b₂ := f ⟨a₂, haU₁ a₂ ha₂⟩) ?_ ?_ ?_ (fun i j hij => hzind k' hk' i j ?_) ⟨_, rfl⟩ ⟨_, rfl⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hfa a₁ ha₁, hfa a₂ ha₂]
      exact (hzc.pow_pow k' k').eq
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hfa a₁ ha₁, Subgroup.coe_one, ← pow_mul, mul_comm, pow_mul,
        hzp a₁ ha₁, one_pow]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hfa a₂ ha₂, Subgroup.coe_one, ← pow_mul, mul_comm, pow_mul,
        hzp a₂ ha₂, one_pow]
    · have := congrArg Subtype.val hij
      rwa [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hfa a₁ ha₁, hfa a₂ ha₂,
        Subgroup.coe_one] at this
  rw [← hcard]
  exact Nat.mul_le_mul_left _ hrange

end Config

end CFSG.StandardType
