module

public import CFSG.Quasithin.Vol2.E2NineTI2bL3Dich
public import CFSG.Quasithin.Vol2.E2NineTI2bL3Norm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Quasithin.Vol2.Ch3E213MP5F
public import CFSG.Quasithin.Vol2.Ch3E213MP5H
public import CFSG.Quasithin.Vol2.E2NineTI2bBase

public section

namespace CFSG.Quasithin.E2.TI2b.L3

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.Ch3E213M.P5

section Model

variable {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal]

theorem model_of_setting_swap {S B E : Subgroup A} {n : ℕ}
    (hS : IsSylowTwoOf S ⊤) (hC : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1)
    (hPSL : IsPSL 3 2 n ↥K)
    (hdiag : ∀ P : Subgroup A, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) ≤ P →
        ¬ S ≤ Subgroup.normalizer (P : Set A))
    (hBorel : ∃ S₀ : Subgroup A, IsSylowTwoOf S₀ K ∧
      B ⊓ K = K ⊓ Subgroup.normalizer (S₀ : Set A))
    (hSB : S ≤ B) (hES : E ≤ S) (hSE : S ≤ Subgroup.normalizer (E : Set A))
    (hE2 : ∀ x ∈ E, x * x = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (θ : ↥K ≃* projectiveSL 3 k),
      Nat.card k = 2 ^ n ∧
      ((S ⊓ K).subgroupOf K).map θ.toMonoidHom = projUnitriangular 3 k ∧
      ((B ⊓ K).subgroupOf K).map θ.toMonoidHom = projUpperTriangular 3 k ∧
      E ≤ ((pzz k).map θ.symm.toMonoidHom).map K.subtype ∧
      ∃ t ∈ S, (pa1 k).map (conjModel θ t).toMonoidHom = pa2 k ∧
        (pa2 k).map (conjModel θ t).toMonoidHom = pa1 k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : IsSylowTwoOf (S ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hS le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨k, _, _, _, θ, hk, hθ, hR, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hPSL
      (isSylowTwoOf_subgroupOf_top hSK)
  have hk' : ∃ m : ℕ, Nat.card k = 2 ^ m := ⟨n, hk⟩
  have hNθ : (Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)).map
      θ.toMonoidHom = projUpperTriangular 3 k := by
    rw [Subgroup.map_equiv_normalizer_eq, hθ, normalizer_projUnitriangular 2]
  obtain ⟨S₀, hS₀, hB⟩ := hBorel
  have hBK := inf_normalizer_eq_of_borel hSK hS₀ hB (le_inf (inf_le_left.trans hSB) inf_le_right)
  have hBθ : ((B ⊓ K).subgroupOf K).map θ.toMonoidHom = projUpperTriangular 3 k := by
    rw [subgroupOf_eq_normalizer hBK, hNθ]
  set P₀ : Subgroup K := (projStabilizer (flagSpace 3 k 1)).map θ.symm.toMonoidHom with hP₀
  have hcov : P₀ ⋖ ⊤ := (hR.2.2.1 _ (hR.2.1 0)).2 ⟨0, rfl⟩
  have hNP : Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K) ≤ P₀ :=
    calc Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)
        = ((Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)).map
            θ.toMonoidHom).map θ.symm.toMonoidHom := (map_symm_map θ _).symm
      _ = (projUpperTriangular 3 k).map θ.symm.toMonoidHom := by rw [hNθ]
      _ ≤ P₀ := Subgroup.map_mono (projUpperTriangular_le_projStabilizer 1)
  obtain ⟨hmax, hle⟩ := isMaxParabolic2_of_isCoatom hSK hcov hNP
  obtain ⟨t, htS, ht⟩ := Set.not_subset.mp (hdiag _ hmax hle)
  have hP : (projStabilizer (flagSpace 3 k 1)).map (conjModel θ t).toMonoidHom ≠
      projStabilizer (flagSpace 3 k 1) := map_conjModel_ne θ ht
  have htU : (projUnitriangular 3 k).map (conjModel θ t).toMonoidHom = projUnitriangular 3 k := by
    rw [← hθ, map_conjModel, map_conjNormal_eq (Subgroup.le_normalizer htS)]
  have hswap := map_pa1_eq_pa2 hk' (conjModel θ t) htU hP
  have htU' : (projUnitriangular 3 k).map (conjModel θ t).symm.toMonoidHom =
      projUnitriangular 3 k := by
    conv_lhs => rw [← htU]
    exact map_symm_map _ _
  have hP' : (projStabilizer (flagSpace 3 k 1)).map (conjModel θ t).symm.toMonoidHom ≠
      projStabilizer (flagSpace 3 k 1) := by
    intro h
    apply hP
    have h1 := map_map_symm (conjModel θ t) (projStabilizer (flagSpace 3 k 1))
    rw [h] at h1
    exact h1
  have hswap' := map_pa1_eq_pa2 hk' (conjModel θ t).symm htU' hP'
  refine ⟨k, inferInstance, inferInstance, inferInstance, θ, hk, hθ, hBθ,
    le_pzz_of_core hk' θ hθ hC ⟨t, htS, hP⟩ hES hSE hE2, t, htS, hswap, ?_⟩
  have h1 := map_map_symm (conjModel θ t) (pa1 k)
  rw [hswap'] at h1
  exact h1

end Model

section Emb

variable {A : Type} [Group A] {K : Subgroup A} [K.Normal] {k : Type} [Field k]

@[expose] def emb (θ : ↥K ≃* projectiveSL 3 k) : projectiveSL 3 k →* A :=
  K.subtype.comp θ.symm.toMonoidHom

theorem emb_injective (θ : ↥K ≃* projectiveSL 3 k) : Function.Injective (emb θ) :=
  K.subtype_injective.comp θ.symm.injective

theorem map_emb (θ : ↥K ≃* projectiveSL 3 k) (X : Subgroup (projectiveSL 3 k)) :
    X.map (emb θ) = (X.map θ.symm.toMonoidHom).map K.subtype := by
  rw [emb, ← Subgroup.map_map]

theorem emb_mem (θ : ↥K ≃* projectiveSL 3 k) (x : projectiveSL 3 k) : emb θ x ∈ K :=
  (θ.symm x).2

theorem range_emb (θ : ↥K ≃* projectiveSL 3 k) : (emb θ).range = K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact emb_mem θ y
  · intro hx
    exact ⟨θ ⟨x, hx⟩, by simp [emb]⟩

theorem emb_conj (θ : ↥K ≃* projectiveSL 3 k) (t : A) (x : projectiveSL 3 k) :
    emb θ (conjModel θ t x) = t * emb θ x * t⁻¹ := by
  simp [emb, conjModel_apply, MulAut.conjNormal_apply]

theorem map_emb_conjModel (θ : ↥K ≃* projectiveSL 3 k) (t : A) (X : Subgroup (projectiveSL 3 k)) :
    (X.map (conjModel θ t).toMonoidHom).map (emb θ) = conjSub t (X.map (emb θ)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [mem_conjSub]
    refine ⟨x, hx, ?_⟩
    have := emb_conj θ t x
    simp only [MulEquiv.coe_toMonoidHom] at *
    rw [this]
    group
  · intro hz
    rw [mem_conjSub] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨conjModel θ t x, ⟨x, hx, rfl⟩, ?_⟩
    show emb θ (conjModel θ t x) = z
    rw [emb_conj, hxz]
    group

theorem conjSub_map {G G' : Type} [Group G] [Group G'] (φ : G →* G') (y : G) (X : Subgroup G) :
    conjSub (φ y) (X.map φ) = (conjSub y X).map φ := by
  ext z
  constructor
  · intro hz
    rw [mem_conjSub] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨y * x * y⁻¹, mem_conjSub.mpr (by simpa [mul_assoc] using hx), ?_⟩
    rw [map_mul, map_mul, map_inv, hxz]
    group
  · rintro ⟨w, hw, rfl⟩
    have hw' : y⁻¹ * w * y ∈ X := mem_conjSub.mp (SetLike.mem_coe.mp hw)
    rw [mem_conjSub]
    exact ⟨y⁻¹ * w * y, hw', by rw [map_mul, map_mul, map_inv]⟩

end Emb

theorem pa1_comm {k : Type} [Field k] {a b : projectiveSL 3 k} (ha : a ∈ pa1 k) (hb : b ∈ pa1 k) :
    a * b = b * a := by
  obtain ⟨_, ⟨a₁, c₁, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨a₂, c₂, rfl⟩, rfl⟩ := hb
  rw [← map_mul, ← map_mul, uu_mul, uu_mul]
  congr 2 <;> ring

theorem dich_conj_pzz {k : Type} [Field k] [Finite k] [CharP k 2] (hk : 4 ≤ Nat.card k)
    (hk2 : ∃ m : ℕ, Nat.card k = 2 ^ m) {Y : Subgroup (projectiveSL 3 k)} (hY : pa1 k ≤ Y)
    {x : projectiveSL 3 k} (hx : conjSub x (pzz k) ≤ pa1 k) : Dich (conjSub x (pzz k)) Y := by
  have hxN := mem_normalizer_pa1_of_conj_pzz_le hk2 hx
  have hY' : pa1 k ≤ conjSub x⁻¹ Y := by
    intro p hp
    rw [mem_conjSub, inv_inv]
    exact hY ((Subgroup.mem_normalizer_iff.mp hxN p).mp hp)
  have h := dich_pzz hk hY'
  have key : conjSub x (conjSub x⁻¹ Y) = Y := by
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  have := dich_conj (x := x) (R := pzz k) (Y := conjSub x⁻¹ Y)
  rw [key] at this
  exact this.mpr h

theorem l3Leaf_holds : L3Leaf := by
  intro A _ _ Ts Ms K Es _ n hn2 hTs hLT hC hPSL hdiag hMK hTsMs hEsTs hEs2 hTsE hMsE hEs1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : IsSylowTwoOf (Ts ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTs le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨k, _, _, _, θ, hk, hθS, hθB, hEZ, t, htT, hsw1, hsw2⟩ :=
    model_of_setting_swap hTs hC hPSL hdiag ⟨Ts ⊓ K, hSK, hMK⟩ hTsMs hEsTs hTsE hEs2
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hk2 : ∃ m : ℕ, Nat.card k = 2 ^ m := ⟨n, hk⟩
  have hφi : Function.Injective (emb θ) := emb_injective θ
  have hUφ : (projUnitriangular 3 k).map (emb θ) = Ts ⊓ K := by
    rw [map_emb, ← hθS, map_symm_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hBφ : (projUpperTriangular 3 k).map (emb θ) = Ms ⊓ K := by
    rw [map_emb, ← hθB, map_symm_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hEφ : Es ≤ (pzz k).map (emb θ) := by rw [map_emb]; exact hEZ
  have hZE : (pzz k).map (emb θ) ≤ Es := by
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEs1
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    obtain ⟨z, hz, rfl⟩ := hEφ he
    have hz1 : z ≠ 1 := fun h => he1' (by rw [h, map_one])
    rintro _ ⟨z', hz', rfl⟩
    by_cases h1' : z' = 1
    · rw [h1', map_one]
      exact Es.one_mem
    obtain ⟨b, hb, hbz⟩ := exists_conj_pzz hz hz' hz1 h1'
    have hbM : emb θ b ∈ Ms := (hBφ ▸ (⟨b, hb, rfl⟩ : emb θ b ∈ (projUpperTriangular 3 k).map
      (emb θ)) : emb θ b ∈ Ms ⊓ K).1
    have := (Subgroup.mem_normalizer_iff.mp (hMsE hbM) (emb θ z)).mp he
    rw [← hbz, map_mul, map_mul, map_inv]
    exact this
  have hEZeq : (pzz k).map (emb θ) = Es := le_antisymm hZE hEφ
  have hEK : Es ≤ K := by
    rw [← hEZeq]
    rintro _ ⟨z, -, rfl⟩
    exact emb_mem θ z
  have hcard : Nat.card Es = 2 ^ n := by
    rw [← hEZeq, Subgroup.card_map_of_injective hφi, card_pzz, hk]
  refine ⟨hEK, hcard, ?_⟩
  have htZ : (pzz k).map (conjModel θ t).toMonoidHom = pzz k := by
    apply Subgroup.map_injective hφi
    rw [map_emb_conjModel, hEZeq, conjSub_eq_self (hTsE htT)]
  set 𝓡 : Set (Subgroup A) := {R | ∃ y : projectiveSL 3 k,
    R = (conjSub y (pzz k)).map (emb θ) ∧ conjSub y (pzz k) ≤ pa1 k} with h𝓡
  refine starDich_of_swap inferInstance hEK htT 𝓡 ?_ ?_
  ·
    intro x hx
    have hxK : x ∈ K ⊔ Ts := hLT ▸ Subgroup.mem_top x
    obtain ⟨κ, hκ, s, hs, rfl⟩ : ∃ κ ∈ K, ∃ s ∈ Ts, κ * s = x := by
      have h1 : x ∈ ((K ⊔ Ts : Subgroup A) : Set A) := hxK
      rw [Subgroup.normal_mul] at h1
      obtain ⟨κ, hκ, s, hs, h⟩ := Set.mem_mul.mp h1
      exact ⟨κ, hκ, s, hs, h⟩
    obtain ⟨y, rfl⟩ : κ ∈ (emb θ).range := by rw [range_emb]; exact hκ
    have hconj : conjSub (emb θ y * s) Es = (conjSub y (pzz k)).map (emb θ) := by
      rw [conjSub_mul, conjSub_eq_self (hTsE hs), ← hEZeq, conjSub_map]
    rw [hconj] at hx ⊢
    have hR'U : conjSub y (pzz k) ≤ projUnitriangular 3 k := by
      rw [← Subgroup.map_le_map_iff_of_injective hφi, hUφ]
      exact le_inf hx (by
        rintro _ ⟨w, -, rfl⟩
        exact emb_mem θ w)
    have h2 : ∀ w ∈ conjSub y (pzz k), w * w = 1 := by
      intro w hw
      have hw' := mul_self_of_mem_pa1 (pzz_le_pa1 (mem_conjSub.mp hw))
      have : w * w = y * ((y⁻¹ * w * y) * (y⁻¹ * w * y)) * y⁻¹ := by group
      rw [this, hw', mul_one, mul_inv_cancel]
    rcases le_or_le_proj hR'U h2 with h | h
    · exact Or.inl ⟨y, rfl, h⟩
    · right
      have h4 : (conjSub y (pzz k)).map (conjModel θ t).toMonoidHom =
          conjSub (conjModel θ t y) (pzz k) := by
        rw [← conjSub_map (conjModel θ t).toMonoidHom y (pzz k), htZ]
        rfl
      refine ⟨conjModel θ t y, ?_, ?_⟩
      · rw [← map_emb_conjModel θ t, h4]
      · rw [← h4]
        exact (Subgroup.map_mono h).trans hsw2.le
  ·
    rintro R ⟨y, rfl, hy⟩ hRT hRK Y hYK hCY
    have hQU : (pa1 k).map (emb θ) ≤ Ts ⊓ K := by
      rw [← hUφ]
      exact Subgroup.map_mono pa1_le
    have hQY : (pa1 k).map (emb θ) ≤ Y := by
      refine fun q hq => hCY ⟨hQU hq, ?_⟩
      show q ∈ Subgroup.centralizer (((conjSub y (pzz k)).map (emb θ) : Subgroup A) : Set A)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hq
      have hb' : b ∈ pa1 k := hy hb
      rw [← map_mul, ← map_mul, pa1_comm hb' ha]
    have hYθ : pa1 k ≤ Y.comap (emb θ) := fun a ha => hQY ⟨a, ha, rfl⟩
    have hYmap : (Y.comap (emb θ)).map (emb θ) = Y := by
      apply Subgroup.map_comap_eq_self
      rw [range_emb]
      exact hYK
    exact dich_of_embedding hφi rfl hYmap (dich_conj_pzz hk4 hk2 hYθ hy)

end CFSG.Quasithin.E2.TI2b.L3
