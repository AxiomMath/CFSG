module

public import CFSG.Quasithin.H13.L32AKGAutM12
public import CFSG.Quasithin.Recognition.M12AmalAutLFacts
public import CFSG.Quasithin.Recognition.M12AmalAutFeit

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv CFSG.Open CFSG.QuasithinUnique

theorem x_conj_Esub_chk :
    ∃ i ∈ eIdx, ∀ j ∈ eIdx, compL (compL (gl 3) (tl i)) (gil 3) ≠ tl j := by
  decide +kernel

theorem Esub_cent_B_chk :
    ∀ i ∈ eIdx, (∀ k ∈ [0, 1, 2, 4], compL (gl k) (tl i) = compL (tl i) (gl k)) → i = 0 := by
  decide +kernel

theorem genG_three_not_mem_normalizer_Esub :
    genG 3 ∉ Subgroup.normalizer (Esub : Set AutG) := by
  intro h
  obtain ⟨i, hi, hne⟩ := x_conj_Esub_chk
  have hi128 := eIdx_chk.2.2.1 i hi
  have hmem : genG 3 * telG i * (genG 3)⁻¹ ∈ Esub :=
    (Subgroup.mem_normalizer_iff.mp h _).mp ⟨i, hi, rfl⟩
  obtain ⟨j, hj, hje⟩ := hmem
  exact hne j hj (conj_gen_idx (by norm_num) hi128 (eIdx_chk.2.2.1 j hj) hje)

theorem Esub_inf_centralizer_B : Esub ⊓ Subgroup.centralizer (autData.B : Set AutG) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨i, hi, rfl⟩, hc⟩
  rw [Subgroup.mem_bot]
  have hi128 := eIdx_chk.2.2.1 i hi
  have h0 : i = 0 := Esub_cent_B_chk i hi fun k hk => by
    have hk5 : k < 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    have hcomm : genG k * telG i = telG i * genG k :=
      Subgroup.mem_centralizer_iff.mp hc _ (genG_mem_B hk)
    have r1 : ReprG (compL (gl k) (tl i)) (genG k * telG i) :=
      reprG_mul (reprG_gen k hk5) (reprG_tel i hi128)
    have r2 : ReprG (compL (tl i) (gl k)) (telG i * genG k) :=
      reprG_mul (reprG_tel i hi128) (reprG_gen k hk5)
    rw [hcomm] at r1
    exact repL_unique r1 r2
  rw [h0, telG_zero_idx]

theorem eq_Esub_of_card {U : Subgroup AutG} (hUT : U ≤ autData.T) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hU : Nat.card U = 16) : U = Esub := by
  have hinv : ∀ u ∈ U, u⁻¹ = u := fun u hu =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u hu)
  have hel : IsElemAbelian 2 U := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, hU2⟩
    have h1 := hinv _ (U.mul_mem x.2 y.2)
    rw [mul_inv_rev, hinv _ y.2, hinv _ x.2] at h1
    exact h1.symm
  obtain ⟨X, hXfam, hX⟩ := elemAbelian_mem_fam _ U hUT hel rfl
  obtain ⟨-, hX16, hnd, hlt, -⟩ := famTab_bound_chk X hXfam
  have hcard := card_of_idx hnd hlt hX
  have hXe : X = eIdx := hX16 (by omega)
  ext g
  rw [hX g, hXe]
  rfl

theorem isSylowTwoOf_top_of {Q : Subgroup AutG} (h1 : IsPGroup 2 ↥Q) (h2 : ¬ 2 ∣ Q.index) :
    IsSylowTwoOf Q ⊤ := by
  refine ⟨le_top, h1, ?_⟩
  rw [show (Q.subgroupOf ⊤).index = Q.index from Subgroup.relIndex_top_right Q]
  exact h2

theorem inf_centralizer_eq_bot_model {T U P : Subgroup AutG} (hT : Nat.card T = 2 ^ 7)
    (hUT : U ≤ T) (hU16 : Nat.card U = 16) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hTP : T ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set AutG)) (hP : Nat.card P = 2 ^ 7 * 3) :
    U ⊓ Subgroup.centralizer (P : Set AutG) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card hT
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 := Subgroup.card_mul_index T
    have h2 := Subgroup.card_mul_index autData.T
    rw [hT] at h1
    rw [aut_card_T] at h2
    have heq : T.index = autData.T.index := by omega
    rw [heq]
    exact aut_syl.2
  have hS₀ : IsSylowTwoOf autData.T ⊤ := isSylowTwoOf_top_of aut_syl.1 aut_syl.2
  have hS : IsSylowTwoOf T ⊤ := isSylowTwoOf_top_of hT2 hTidx
  obtain ⟨h, -, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hS₀ hS
  set φ : AutG ≃* AutG := MulAut.conj h⁻¹ with hφ
  have hφx : ∀ x : AutG, φ x = h⁻¹ * x * h := fun x => by
    rw [hφ, MulAut.conj_apply, inv_inv]
  set U₁ := U.map φ.toMonoidHom with hU₁
  set P₁ := P.map φ.toMonoidHom with hP₁
  have hmemU₁ : ∀ x, x ∈ U → φ x ∈ U₁ := fun x hx => ⟨x, hx, rfl⟩
  have hU₁T : U₁ ≤ autData.T := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ∈ autData.T
    rw [hφx]
    exact (hconj x).mp (hUT hx)
  have hTP₁ : autData.T ≤ P₁ := by
    intro y hy
    have hy' : h * y * h⁻¹ ∈ T := (hconj _).mpr (by
      rw [show h⁻¹ * (h * y * h⁻¹) * h = y by group]
      exact hy)
    refine ⟨h * y * h⁻¹, hTP hy', ?_⟩
    show φ (h * y * h⁻¹) = y
    rw [hφx]
    group
  have hU₁16 : Nat.card U₁ = 16 := by
    rw [hU₁, Subgroup.card_map_of_injective φ.injective, hU16]
  have hP₁card : Nat.card P₁ = 2 ^ 7 * 3 := by
    rw [hP₁, Subgroup.card_map_of_injective φ.injective, hP]
  have hU₁2 : ∀ u ∈ U₁, u ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ^ 2 = 1
    rw [← map_pow, hU2 x hx, map_one]
  have hP₁U : P₁ ≤ Subgroup.normalizer (U₁ : Set AutG) :=
    (Subgroup.map_mono hPU).trans (Subgroup.le_normalizer_map _)
  have hUE : U₁ = Esub := eq_Esub_of_card hU₁T hU₁2 hU₁16
  rw [hUE] at hP₁U
  have hPB : P₁ = autData.B := by
    rcases autData.lattice P₁ hTP₁ with h1 | h1 | h1 | h1
    · exfalso
      have := aut_card_T
      rw [← h1, hP₁card] at this
      omega
    · exfalso
      exact genG_three_not_mem_normalizer_Esub (hP₁U (h1 ▸ autData.x_mem_A))
    · exact h1
    · exfalso
      exact genG_three_not_mem_normalizer_Esub (hP₁U (h1 ▸ Subgroup.mem_top _))
  rw [eq_bot_iff]
  rintro u ⟨huU, huP⟩
  rw [Subgroup.mem_bot]
  have huP' : u ∈ Subgroup.centralizer (P : Set AutG) := huP
  have h1 : φ u ∈ Esub ⊓ Subgroup.centralizer (autData.B : Set AutG) := by
    refine ⟨hUE ▸ hmemU₁ u huU, ?_⟩
    show φ u ∈ Subgroup.centralizer (autData.B : Set AutG)
    rw [← hPB, Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    show φ p * φ u = φ u * φ p
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp huP' p hp]
  rw [Esub_inf_centralizer_B, Subgroup.mem_bot] at h1
  exact φ.injective (h1.trans (map_one φ).symm)

end CFSG.Quasithin.M12AmalAut

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.M12AmalAut

theorem kgAutM12E16 :
    KGAutM12E16 := by
  intro A _ _ hA T U P hT hUT hTU hU16 hU2 hTP hPU hP
  obtain ⟨φ⟩ := hA
  obtain ⟨ψ⟩ := autM12PermModel
  set e : A ≃* AutG := φ.trans ψ.symm with he
  have hmap : ∀ (H : Subgroup A), Nat.card (H.map e.toMonoidHom) = Nat.card H := fun H =>
    Subgroup.card_map_of_injective e.injective
  have key := inf_centralizer_eq_bot_model (T := T.map e.toMonoidHom) (U := U.map e.toMonoidHom)
    (P := P.map e.toMonoidHom) (by rw [hmap, hT]) (Subgroup.map_mono hUT) (by rw [hmap, hU16])
    (by
      rintro _ ⟨u, hu, rfl⟩
      show e u ^ 2 = 1
      rw [← map_pow, hU2 u hu, map_one])
    (Subgroup.map_mono hTP) ((Subgroup.map_mono hPU).trans (Subgroup.le_normalizer_map _))
    (by rw [hmap, hP])
  rw [eq_bot_iff]
  rintro u ⟨huU, huP⟩
  rw [Subgroup.mem_bot]
  have huP' : u ∈ Subgroup.centralizer (P : Set A) := huP
  have h1 : e u ∈ U.map e.toMonoidHom ⊓ Subgroup.centralizer
      ((P.map e.toMonoidHom : Subgroup AutG) : Set AutG) := by
    refine ⟨⟨u, huU, rfl⟩, ?_⟩
    show e u ∈ Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup AutG) : Set AutG)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    show e p * e u = e u * e p
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp huP' p hp]
  rw [key, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

end CFSG.Quasithin.H13
