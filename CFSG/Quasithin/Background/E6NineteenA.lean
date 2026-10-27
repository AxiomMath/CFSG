module

public import CFSG.Quasithin.Background.E6Nineteen
public import CFSG.Quasithin.Background.GoldschmidtTDE68CovBase

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def OddInvertFree (X : Type*) [Group X] : Prop :=
  ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∀ α β δ : MulAut X, α * α = 1 → α ≠ 1 →
    (∀ s ∈ S, α s = s) → β * β = 1 → (∀ s ∈ S, β s = s) → α * β = β * α →
    Odd (orderOf δ) → δ * α = α * δ → β⁻¹ * δ * β = δ⁻¹ → δ = 1

section Core

variable {X : Type*} [Group X]

theorem eq_one_of_sq_of_odd {M : Type*} [Monoid M] {δ : M} (hodd : Odd (orderOf δ))
    (h : δ * δ = 1) : δ = 1 := by
  have hd := orderOf_dvd_of_pow_eq_one (show δ ^ 2 = 1 by rw [pow_two]; exact h)
  have h1 : orderOf δ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

theorem eq_one_of_eq_one_or_eq {α β δ : MulAut X} (hβ : β = 1 ∨ β = α) (hodd : Odd (orderOf δ))
    (hδα : δ * α = α * δ) (hinv : β⁻¹ * δ * β = δ⁻¹) : δ = 1 := by
  apply eq_one_of_sq_of_odd hodd
  have h1 : δ = δ⁻¹ := by
    rcases hβ with rfl | rfl
    · simpa using hinv
    · rw [← hinv, mul_assoc, hδα, ← mul_assoc, inv_mul_cancel, one_mul]
  calc δ * δ = δ * δ⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel δ

theorem mulAut_mul_conj_mul_inv (φ : MulAut X) (g : X) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_eq_one_iff_mem_center (g : X) : MulAut.conj g = 1 ↔ g ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut X => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x, mul_inv_cancel_right]

variable [Finite X]

theorem mem_center_of_conj (hZ : Subgroup.center X = ⊥) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    {t : X} (hfix : ∀ s ∈ S, MulAut.conj t s = s) (h2 : MulAut.conj t * MulAut.conj t = 1) :
    t ∈ S ∧ t ∈ Subgroup.centralizer (S : Set X) ∧ t * t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by
    have h1 : MulAut.conj (t * t) = 1 := by rw [map_mul, h2]
    rw [conj_eq_one_iff_mem_center, hZ, Subgroup.mem_bot] at h1
    exact h1
  have hC : t ∈ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hfix s hs
    rw [MulAut.conj_apply] at h1
    calc s * t = t * s * t⁻¹ * t := by rw [h1]
      _ = t * s := by group
  refine ⟨?_, hC, htt⟩
  by_cases ht1 : t = 1
  · rw [ht1]
    exact S.one_mem
  have h2t : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ hC
  have hP : IsPGroup 2 (S ⊔ Subgroup.zpowers t : Subgroup X) :=
    hS.isPGroup.to_sup_of_normal_left' h2t hN
  have heq := hS.eq_of_le le_sup_left le_top hP
  rw [← heq]
  exact (le_sup_right : Subgroup.zpowers t ≤ S ⊔ _) (Subgroup.mem_zpowers t)

theorem exists_conj_of_involFixInner (hZ : Subgroup.center X = ⊥) (hinn : Inn.InvolFixInner X)
    {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) {β : MulAut X} (h2 : β * β = 1)
    (hfix : ∀ s ∈ S, β s = s) :
    ∃ t : X, β = MulAut.conj t ∧ t ∈ S ∧ t ∈ Subgroup.centralizer (S : Set X) ∧ t * t = 1 := by
  have hinv : ∀ w, β (β w) = w := fun w => by
    have := congrArg (fun φ : MulAut X => φ w) h2
    simpa using this
  obtain ⟨x, hx⟩ := hinn S hS β hinv hfix
  have hβ : β = MulAut.conj x⁻¹ := by
    ext w
    rw [hx w, MulAut.conj_apply, inv_inv]
  refine ⟨x⁻¹, hβ, ?_⟩
  rw [hβ] at hfix h2
  exact mem_center_of_conj hZ hS hfix h2

theorem oddInvertFree_of_cyclic (hZ : Subgroup.center X = ⊥) (hinn : Inn.InvolFixInner X)
    (hcyc : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → IsCyclic (Subgroup.center ↥S)) :
    OddInvertFree X := by
  classical
  intro S hS α β δ hα2 hα1 hαS hβ2 hβS _ hodd hδα hinv
  obtain ⟨t, rfl, htS, htC, htt⟩ := exists_conj_of_involFixInner hZ hinn hS hα2 hαS
  obtain ⟨t', rfl, ht'S, ht'C, ht't⟩ := exists_conj_of_involFixInner hZ hinn hS hβ2 hβS
  refine eq_one_of_eq_one_or_eq ?_ hodd hδα hinv
  have hcen : ∀ (y : X) (hyS : y ∈ S), y ∈ Subgroup.centralizer (S : Set X) →
      (⟨y, hyS⟩ : ↥S) ∈ Subgroup.center ↥S := fun y hyS hyC => by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyC w w.2)
  have := hcyc S hS
  have : Fintype ↥(Subgroup.center ↥S) := Fintype.ofFinite _
  set a : ↥(Subgroup.center ↥S) := ⟨⟨t, htS⟩, hcen t htS htC⟩
  set b : ↥(Subgroup.center ↥S) := ⟨⟨t', ht'S⟩, hcen t' ht'S ht'C⟩
  have ha1 : a ≠ 1 := fun h => hα1 (by
    have : t = 1 := congrArg (fun w : ↥(Subgroup.center ↥S) => ((w : ↥S) : X)) h
    rw [this, map_one])
  have ha2 : a ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [a, pow_two, htt]))
  have hb2 : b ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [b, pow_two, ht't]))
  have hcard := IsCyclic.card_pow_eq_one_le (α := ↥(Subgroup.center ↥S)) (n := 2) (by norm_num)
  by_contra hne
  push Not at hne
  obtain ⟨hb1, hba⟩ := hne
  have hb1' : b ≠ 1 := fun h => hb1 (by
    have : t' = 1 := congrArg (fun w : ↥(Subgroup.center ↥S) => ((w : ↥S) : X)) h
    rw [this, map_one])
  have hba' : b ≠ a := fun h => hba (by
    have : t' = t := congrArg (fun w : ↥(Subgroup.center ↥S) => ((w : ↥S) : X)) h
    rw [this])
  have hsub : ({1, a, b} : Finset ↥(Subgroup.center ↥S)) ⊆
      Finset.univ.filter (fun x : ↥(Subgroup.center ↥S) => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact ha2
    · exact hb2
  have h3 : ({1, a, b} : Finset ↥(Subgroup.center ↥S)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hba'.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ha1.symm, hb1'.symm⟩
  have := Finset.card_le_card hsub
  omega

omit [Finite X] in
theorem eq_one_of_charTwo (hZ : Subgroup.center X = ⊥) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    {t t' : X} (htS : t ∈ S) (htC : t ∈ Subgroup.centralizer (S : Set X))
    (ht'C : t' ∈ Subgroup.centralizer (S : Set X))
    (hchar : CFSG.IsCharacteristicP 2 ↥(Subgroup.centralizer ({t} : Set X)))
    {δ : MulAut X} (hodd : Odd (orderOf δ)) (hδα : δ * MulAut.conj t = MulAut.conj t * δ)
    (hinv : (MulAut.conj t')⁻¹ * δ * MulAut.conj t' = δ⁻¹) : δ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set X) with hCdef
  have hδt : δ t = t := by
    have h1 : MulAut.conj (δ t) = MulAut.conj t := by
      rw [← mulAut_mul_conj_mul_inv, hδα, mul_inv_cancel_right]
    have h2 : MulAut.conj (δ t * t⁻¹) = 1 := by rw [map_mul, h1, map_inv, mul_inv_cancel]
    rw [conj_eq_one_iff_mem_center, hZ, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  have hδt' : δ⁻¹ t = t := by
    calc δ⁻¹ t = δ⁻¹ (δ t) := by rw [hδt]
      _ = t := MulAut.inv_apply_self _ δ t
  have hmemC : ∀ φ : MulAut X, φ t = t → ∀ c ∈ C, φ c ∈ C := by
    intro φ hφ c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← hφ, ← map_mul, ← map_mul, hc]
  let δC : MulAut ↥C :=
    { toFun := fun c => ⟨δ (c : X), hmemC δ hδt c c.2⟩
      invFun := fun c => ⟨δ⁻¹ (c : X), hmemC δ⁻¹ hδt' c c.2⟩
      left_inv := fun c => Subtype.ext (MulAut.inv_apply_self _ δ (c : X))
      right_inv := fun c => Subtype.ext (MulAut.apply_inv_self _ δ (c : X))
      map_mul' := fun a b => Subtype.ext (map_mul δ (a : X) (b : X)) }
  set N := CFSG.pCore 2 ↥C with hNdef
  have hδN : ∀ n ∈ N, δC n ∈ N := by
    intro n hn
    have h1 : N.comap δC.toMonoidHom = N :=
      (CFSG.pCore_characteristic (p := 2) (G := ↥C)).fixed δC
    have h2 : n ∈ N.comap δC.toMonoidHom := by rw [h1]; exact hn
    exact h2
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 htC s hs)
  have hSyl : IsSylowTwoOf S C := by
    refine ⟨hSC, hS.isPGroup, fun h2 => hS.2.2 ?_⟩
    have h1 := Subgroup.relIndex_mul_index hSC
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [h3, ← h1]
    exact Dvd.dvd.mul_right h2 _
  have hS2 : IsPGroup 2 (S.subgroupOf C) :=
    hSyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.le).symm
  have hNS : ∀ n ∈ N, ((n : ↥C) : X) ∈ S := by
    intro n hn
    have hle := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).le_sylow_of_normal
      (hS2.toSylow hSyl.2.2)
    exact hle hn
  have ht'C' : t' ∈ C := Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 ht'C t htS).symm
  have ht'N : (⟨t', ht'C'⟩ : ↥C) ∈ N := by
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 ht'C _ (hNS n hn))
  set w : ↥C := (δC ⟨t', ht'C'⟩)⁻¹ * ⟨t', ht'C'⟩ with hw
  have hwN : w ∈ N := N.mul_mem (N.inv_mem (hδN _ ht'N)) ht'N
  have hsq : δ * δ = MulAut.conj (w : X) := by
    set γ := MulAut.conj t' with hγ
    have h2 : γ⁻¹ * δ⁻¹ * γ = δ := by
      rw [show γ⁻¹ * δ⁻¹ * γ = (γ⁻¹ * δ * γ)⁻¹ by group, hinv, inv_inv]
    have h3 : MulAut.conj (w : X) = (δ * γ * δ⁻¹)⁻¹ * γ := by
      rw [mulAut_mul_conj_mul_inv, hw, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rfl
    rw [h3]
    calc δ * δ = δ * (γ⁻¹ * δ⁻¹ * γ) := by rw [h2]
      _ = (δ * γ * δ⁻¹)⁻¹ * γ := by group
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)) ⟨w, hwN⟩
  have hwk : (w : X) ^ 2 ^ k = 1 := by
    have := congrArg (fun v : ↥N => ((v : ↥C) : X)) hk
    simpa using this
  have hδk : δ ^ (2 * 2 ^ k) = 1 := by
    rw [pow_mul, pow_two, hsq, ← map_pow, hwk, map_one]
  have hd := orderOf_dvd_of_pow_eq_one hδk
  rw [← pow_succ'] at hd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' hj0).2 even_two)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.1 hj

theorem oddInvertFree_of_charTwo (hZ : Subgroup.center X = ⊥) (hinn : Inn.InvolFixInner X)
    (hchar : ∀ t : X, t ≠ 1 → t * t = 1 →
      CFSG.IsCharacteristicP 2 ↥(Subgroup.centralizer ({t} : Set X))) :
    OddInvertFree X := by
  intro S hS α β δ hα2 hα1 hαS hβ2 hβS _ hodd hδα hinv
  obtain ⟨t, rfl, htS, htC, htt⟩ := exists_conj_of_involFixInner hZ hinn hS hα2 hαS
  obtain ⟨t', rfl, -, ht'C, -⟩ := exists_conj_of_involFixInner hZ hinn hS hβ2 hβS
  have ht1 : t ≠ 1 := fun h => hα1 (by rw [h, map_one])
  exact eq_one_of_charTwo hZ hS htS htC ht'C (hchar t ht1 htt) hodd hδα hinv

end Core

theorem OddInvertFree.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : OddInvertFree X') : OddInvertFree X := by
  intro S hS α β δ hα2 hα1 hαS hβ2 hβS hαβ hodd hδα hinv
  set c := MulAut.congr e with hc
  have hc_apply : ∀ (φ : MulAut X) (x : X), c φ (e x) = e (φ x) := fun φ x => by
    simp [hc, MulAut.congr_apply]
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map e.toMonoidHom, ?_⟩
    have h1 : ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have h2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective S]
    have := hS.2.2
    rwa [h2] at this
  have hfix' : ∀ φ : MulAut X, (∀ s ∈ S, φ s = s) → ∀ s ∈ S.map e.toMonoidHom, c φ s = s := by
    rintro φ hφ _ ⟨s, hs, rfl⟩
    exact (hc_apply φ s).trans (congrArg e (hφ s hs))
  have hδ := h _ hS' (c α) (c β) (c δ) (by rw [← map_mul, hα2, map_one])
    (fun h1 => hα1 (c.injective (by rw [h1, map_one]))) (hfix' α hαS)
    (by rw [← map_mul, hβ2, map_one]) (hfix' β hβS) (by rw [← map_mul, ← map_mul, hαβ])
    (by rw [MulEquiv.orderOf_eq]; exact hodd) (by rw [← map_mul, ← map_mul, hδα])
    (by rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv])
  exact c.injective (by rw [hδ, map_one])

open Bar in
theorem e619Insp_of_oddInvertFree
    (hfree : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (z : Y), CFSG.IsQuasisimple ↥K →
      Lemma115Cases K z → ¬ Lemma115CaseD K z → OddInvertFree (Qbar K)) :
    E619Insp := by
  intro Y _ _ K R D z u hKq hcases hR hRN hRK hzR hzC hz2 huR huC hu2 huK hDodd hDN hDu hinv hDK
  by_cases hD : Lemma115CaseD K z
  · obtain ⟨φ, -, hZ, -, -⟩ := hD
    exact ⟨⟨φ⟩, hZ⟩
  exfalso
  have hperf : Group.IsPerfect ↥K := hKq.1
  have hE : E68CentHyp K R u :=
    { quasisimple := hKq
      isPGroup := hR
      normalizer := hRN
      sylow := hRK
      mem := huR
      central := fun r hr => (Subgroup.mem_centralizer_iff.1 huC r hr).symm
      sq := hu2
      not_mem := huK }
  obtain ⟨d, hdD, hdK⟩ : ∃ d ∈ D, d ∉ Subgroup.centralizer (K : Set Y) := Set.not_subset.1 hDK
  set u' : ↥(Subgroup.normalizer (K : Set Y)) := ⟨u, hRN huR⟩ with hu'
  set z' : ↥(Subgroup.normalizer (K : Set Y)) := ⟨z, hRN hzR⟩ with hz'
  set d' : ↥(Subgroup.normalizer (K : Set Y)) := ⟨d, hDN hdD⟩ with hd'
  have hfixR : ∀ (r : ↥(Subgroup.normalizer (K : Set Y))),
      (r : Y) ∈ Subgroup.centralizer (R : Set Y) →
      ∀ s ∈ ((R ⊓ K).subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)),
        barHom K r s = s := by
    rintro r hr _ ⟨p, hp, rfl⟩
    exact barHom_mk_of_comm r p
      (Subgroup.mem_centralizer_iff.1 hr p (Subgroup.mem_inf.mp hp).1).symm
  have hsq : ∀ (r : ↥(Subgroup.normalizer (K : Set Y))), (r : Y) ^ 2 = 1 →
      barHom K r * barHom K r = 1 := fun r hr => by
    rw [← map_mul, show r * r = 1 from Subtype.ext (by simpa [pow_two] using hr), map_one]
  have hδ := hfree Y K z hKq hcases hD _ (Inn.isSylowTwoOf_map_mk hE) (barHom K u') (barHom K z')
    (barHom K d') (hsq u' hu2) (fun h1 => huK ?_) (hfixR u' huC) (hsq z' hz2) (hfixR z' hzC)
    ?_ ?_ ?_ ?_
  · apply hdK
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((barHom_eq_one_iff hperf d').1 hδ ⟨k, hk⟩).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((barHom_eq_one_iff hperf u').1 h1 ⟨k, hk⟩).symm
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 huC z hzR).symm
  · have h1 : orderOf d' ∣ Nat.card D := by
      have h2 : orderOf d' = orderOf (⟨d, hdD⟩ : ↥D) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rw [h2]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (Odd.of_dvd_nat hDodd h1) (orderOf_map_dvd _ _)
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hDu hdD))
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (hinv d hdD)

end E6

end CFSG.Quasithin
