module

public import CFSG.Quasithin.Background.SmithB42U33Iso

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B42U33 JonesParshall

variable {V : Type} [CommGroup V] {X K : Subgroup (MulAut V)}

theorem exists_embedding_of_le
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hP : B42TypeU33 ↥K) :
    ∃ ψ : ↥X →* ↥(quasithinG2 (ZMod 2)), Function.Injective ψ ∧
      (∀ g : ↥X, (g : MulAut V) ∈ K → ψ g ∈ g2Derived (ZMod 2)) ∧
      ∀ δ ∈ g2Derived (ZMod 2), ∃ g : ↥X, (g : MulAut V) ∈ K ∧ ψ g = δ := by
  have hK'n : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hXN
  obtain ⟨θ⟩ := nonempty_equiv_g2Derived hP
  let θ' : ↥(K.subgroupOf X) ≃* ↥(g2Derived (ZMod 2)) :=
    (Subgroup.subgroupOfEquivOfLe hKX).trans θ
  refine ⟨embG conjNormal_bijective θ', ?_, fun g hg => ?_, fun δ hδ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hc := embG_eq_one conjNormal_bijective θ' hg
    have hcomm : ∀ x ∈ K, x * (g : MulAut V) = (g : MulAut V) * x := by
      intro x hx
      have h1 := congrArg Subtype.val (hc ⟨x, hKX hx⟩ hx)
      change (g : MulAut V) * x * (g : MulAut V)⁻¹ = x at h1
      calc x * (g : MulAut V) = (g : MulAut V) * x * (g : MulAut V)⁻¹ * g := by rw [h1]
        _ = (g : MulAut V) * x := by group
    have hgK : (g : MulAut V) ∈ K :=
      hCK ⟨g.2, Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx⟩
    have hgZ : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2)
    rw [hP.1, Subgroup.mem_bot] at hgZ
    have h1 : (g : MulAut V) = 1 := congrArg (fun y : ↥K => (y : MulAut V)) hgZ
    exact Subtype.ext h1
  · have := embG_coe conjNormal_bijective θ' ⟨g, hg⟩
    rw [this]
    exact (θ' _).2
  · refine ⟨θ'.symm ⟨δ, hδ⟩, (θ'.symm ⟨δ, hδ⟩).2, ?_⟩
    rw [embG_coe conjNormal_bijective, MulEquiv.apply_symm_apply]

theorem short_generation_of_le
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hP : B42TypeU33 ↥K)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ K) ∧
        K ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) := by
  obtain ⟨ψ, hψ, hψK, hψD⟩ := exists_embedding_of_le hKX hXN hCK hP
  set A' : Subgroup ↥X := A.subgroupOf X with hA'
  set B : Subgroup ↥(quasithinG2 (ZMod 2)) := A'.map ψ with hBdef
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have h1 : ψ ⟨a, hAX ha⟩ ∈ B := ⟨⟨a, hAX ha⟩, ha, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ψ] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (hψ h1)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAe.1 _ ha _ hb)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, ← map_one ψ]
    congr 1
    exact Subtype.ext (hAe.2 _ ha)
  obtain ⟨r, m, hr, hr1, hr3, hmr, d, hd, hle⟩ := shortGen hB1 hBc hB2
  choose l hlK hld using fun i => hψD (d i) (hd i)
  refine ⟨r, m, ?_, hr1, hr3, hmr, fun i => (l i : MulAut V), hlK, ?_⟩
  · rw [← hr, hBdef, Subgroup.card_map_of_injective hψ]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv).symm
  · have hmap : ∀ i, B.map (MulAut.conj (d i)).toMonoidHom =
        (A'.map (MulAut.conj (l i)).toMonoidHom).map ψ := by
      intro i
      rw [hBdef, Subgroup.map_map, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun a => ?_
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_mul, map_inv, ← hld i]
    intro y hy
    have hy' := hle (hψK ⟨y, hKX hy⟩ hy)
    simp only [hmap, Subgroup.coe_map] at hy'
    rw [← Set.image_iUnion, ← MonoidHom.map_closure] at hy'
    · obtain ⟨z, hz, hzy⟩ := hy'
      have hzy' : z = ⟨y, hKX hy⟩ := hψ hzy
      have h1 := Subgroup.mem_map_of_mem X.subtype hz
      rw [MonoidHom.map_closure, hzy'] at h1
      refine Subgroup.closure_mono ?_ h1
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨a, ha, rfl⟩ := hi
      exact Set.mem_iUnion.2 ⟨i, ⟨(a : MulAut V), ha, rfl⟩⟩

theorem index_fixV_le_pow [Finite V] {A : Subgroup (MulAut V)} {m : ℕ} (l : Fin m → MulAut V)
    (hle : K ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
      Subgroup (MulAut V)) : Set (MulAut V)))) :
    (fixV K).index ≤ (fixV A).index ^ m := by
  have hinf : (⨅ i, fixV (A.map (MulAut.conj (l i)).toMonoidHom)) ≤ fixV K := by
    refine (HatA6.iInf_fixV_le_fixV_closure _).trans ?_
    intro v hv x hx
    exact hv x (hle hx)
  have h1 := Subgroup.index_iInf_le (fun i => fixV (A.map (MulAut.conj (l i)).toMonoidHom))
  have h2 : ∀ i, (fixV (A.map (MulAut.conj (l i)).toMonoidHom)).index = (fixV A).index := by
    intro i
    have e1 := (fixV (A.map (MulAut.conj (l i)).toMonoidHom)).card_mul_index
    have e2 := (fixV A).card_mul_index
    rw [HatA6.card_fixV_conj] at e1
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact (Subgroup.index_antitone hinf).trans h1

theorem index_fixV_le_of_index_le_sq [Finite V]
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hP : B42TypeU33 ↥K)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hidx : (fixV A).index ≤ Nat.card A ^ 2) : (fixV K).index ≤ 2 ^ 12 := by
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle⟩ := short_generation_of_le hKX hXN hCK hP hAX hA1 hAe
  refine (index_fixV_le_pow l hle).trans ((Nat.pow_le_pow_left hidx m).trans ?_)
  rw [hr, ← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end CFSG.Quasithin.H13.L32A.M753
