module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Conj
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Toral
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TableBExc.E6Three E6ThreeEnd NoOffTwE6Three

variable {K : Type} [Field K]

theorem slTwoAt_of_le_hatAut [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card X) : SLTwoAt 3 X := by
  have h3' : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact h3
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  set κ := hatAut .E6 K with hκ
  set Y : Subgroup (hatGroup .E6 K) := X.comap κ with hY
  set f : Y →* X := (κ.comp Y.subtype).codRestrict X (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hXI hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hXp : IsPGroup 3 (⊤ : Subgroup X) := fun g => by
    obtain ⟨k, hk⟩ := TableB.isPGroup_of_isElemAbelian hX ⟨g.1, g.1.2⟩
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hXp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPX : P.map κ = X := by
    have hcomp : κ.comp Y.subtype = X.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3') hP3
  set P' := P.map (MulAut.conj c).toMonoidHom with hP'
  set E : Subgroup (ModGL .E6 K) := P'.map (hatGroup .E6 K).subtype with hEdef
  have hEX : E ≤ xHat .E6 K modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hc hp)
  have hker : ∀ p ∈ P', κ p = 1 → p = 1 := fun p hp h1 =>
    eq_one_of_hatAut_eq_one (xHat_le_monoHat _ (hEX ⟨p, hp, rfl⟩)) h1
  have hP'X : P'.map κ = X.map (MulAut.conj (κ c)).toMonoidHom := by
    have hcomp : κ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (κ c)).toMonoidHom.comp κ :=
      MonoidHom.ext fun p => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    rw [hP', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPX]
  have hcardP' : Nat.card P' = Nat.card X := by
    rw [← card_map_eq_of_ker κ hker, hP'X,
      Subgroup.card_map_of_injective (MulAut.conj (κ c)).injective]
  have hXc : IsElemAbelian 3 (X.map (MulAut.conj (κ c)).toMonoidHom) :=
    TableB.isElemAbelian_map hX _
  have hP'ab : ∀ p ∈ P', ∀ p' ∈ P', p * p' = p' * p := by
    intro p hp p' hp'
    have h1 : κ (p * p' * (p' * p)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        TableB.IsElemAbelian.comm hXc (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
          (hP'X ▸ ⟨p', hp', rfl⟩ : κ p' ∈ _), mul_inv_cancel]
    have h2 := hker _ (mul_mem (mul_mem hp hp') (inv_mem (mul_mem hp' hp))) h1
    exact mul_inv_eq_one.mp h2
  have hP'3 : ∀ p ∈ P', p ^ 3 = 1 := by
    intro p hp
    refine hker _ (pow_mem hp 3) ?_
    rw [map_pow]
    exact hXc.2 _ (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
  have hP'el : IsElemAbelian 3 P' :=
    ⟨⟨⟨fun a b => Subtype.ext (hP'ab a a.2 b b.2)⟩⟩, hP'3⟩
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map hP'el _
  have hcardE : Nat.card E = Nat.card X := by
    rw [hEdef, Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective, hcardP']
  have hE5 : 3 ^ 5 ≤ Nat.card E := hcardE ▸ h5
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3'
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨g, hg⟩ : ∃ g : hatGroup .E6 K, ∀ p ∈ P', ∃ b,
      ((g * p * g⁻¹ : hatGroup .E6 K) : ModGL .E6 K) = rootDiagUnit .E6 b := by
    rcases torus_or_cyclic hζo hζ hE hEX hE5 with htor | ⟨i, hi⟩
    · refine ⟨1, fun p hp => ?_⟩
      obtain ⟨v, hv⟩ := htor (p : ModGL .E6 K) ⟨p, hp, rfl⟩
      exact ⟨zetaVec ζ hζ v, by rw [one_mul, inv_one, mul_one]; exact hv⟩
    · obtain ⟨y, hy, hyE⟩ := exists_conj_diag_of_le_xHat hζo hE hi
      exact ⟨⟨y, adjointGroup_le_hatGroup hy⟩, fun p hp => hyE (p : ModGL .E6 K) ⟨p, hp, rfl⟩⟩
  set P'' := P'.map (MulAut.conj g).toMonoidHom with hP''
  have h5'' : 3 ^ 5 ≤ Nat.card P'' := by
    rw [hP'', Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardP']
    exact h5
  have hcore := slTwoAt_toral hK h3 (E := P'') (by rintro _ ⟨p, hp, rfl⟩; exact hg p hp)
    (by rintro _ ⟨p, hp, rfl⟩; rw [← map_pow, hP'3 p hp, map_one]) h5''
  have hcompg : κ.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (κ g)).toMonoidHom.comp κ :=
    MonoidHom.ext fun p => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
  have hcomp2 : (MulAut.conj (κ g)).toMonoidHom.comp (MulAut.conj (κ c)).toMonoidHom =
      (MulAut.conj (κ (g * c))).toMonoidHom := MonoidHom.ext fun φ => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, MulAut.mul_apply]
  have hmapX : P''.map κ = X.map (MulAut.conj (κ (g * c))).toMonoidHom := by
    rw [hP'', Subgroup.map_map, hcompg, ← Subgroup.map_map, hP'X, Subgroup.map_map, hcomp2]
  rw [hmapX] at hcore
  have h := hcore.map (κ (g * c))⁻¹
  rwa [map_congr_inv_map_conj] at h

theorem ggStdSubTwoTorusSLTwoAut_hat [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGStdSubTwoTorusSLTwoAut 3 5 (adjointGroup .E6 K) (Set.range (hatAut .E6 K)) :=
  ggStdSubTwoTorusSLTwoAut_of_forall fun _ hX hXI h5 =>
    slTwoAt_of_le_hatAut hK h3 hX (fun φ hφ => hXI φ hφ) h5

end CFSG.StandardType.SmallExc

end
