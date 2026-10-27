module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.GroupTheory.SylowEmbedding
import CFSG.LocalAnalysis.WeakClosure81.GenEiConj
import CFSG.LocalAnalysis.WeakClosure81.InCalEOneMembers
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen
import CFSG.Quasithin.EmptyFaithful.T1531In68b
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def FourTenMember {Y : Type} [Group Y] (G T₀ B : Subgroup Y) : Prop :=
  (∃ K : Subgroup Y, K ≤ G ∧ T₀ ⊓ centralizer (B : Set Y) ≤ K ∧
      Nat.card K = 3 * Nat.card (K ⊓ T₀ : Subgroup Y) ∧
      ¬ K ≤ normalizer ((K ⊓ T₀ : Subgroup Y) : Set Y) ∧ ¬ B ≤ pCoreOf 2 K ∧ K ⊔ T₀ = G) ∨
    ∃ x ∈ G, orderOf x = 5 ∧ T₀ ⊓ centralizer (B : Set Y) ≤ normalizer (zpowers x : Set Y) ∧
      (∃ b ∈ B, b * x ≠ x * b) ∧ zpowers x ⊔ T₀ = G

structure FourTenModel {Y : Type} [Group Y] (G T₀ : Subgroup Y) : Prop where
  sylow : IsSylowIn 2 T₀ G
  member : ∀ A : Subgroup Y, A ≤ T₀ → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    ∃ g ∈ G, A.map (MulAut.conj g).toMonoidHom ≤ T₀ ∧
      FourTenMember G T₀ (A.map (MulAut.conj g).toMonoidHom)

private theorem map_tA_le_centralizer {Q Y : Type} [Group Q] [Group Y]
    {T : Subgroup Q} {T₀ : Subgroup Y} {ι' : Q →* Y} {A' : Subgroup Q} {Bg : Subgroup Y}
    (hmapT : T.map ι' = T₀) (hA'map : A'.map ι' = Bg)
    (hτ : tA T A' = T ⊓ centralizer (A' : Set Q)) :
    (tA T A').map ι' ≤ T₀ ⊓ centralizer (Bg : Set Y) := by
  refine le_inf ?_ ?_
  · calc (tA T A').map ι' ≤ T.map ι' := Subgroup.map_mono (hτ ▸ inf_le_left)
      _ = T₀ := hmapT
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    obtain ⟨t, ht, rfl⟩ := hy
    have ht' : t ∈ Subgroup.centralizer (A' : Set Q) := by
      rw [hτ] at ht
      exact ht.2
    intro b hb
    rw [← hA'map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp ht' a ha]

private theorem genEi_sup_eq_top_of_sThree {Q Y : Type} [Group Q] [Finite Q] [Group Y]
    [Finite Y] {G T₀ : Subgroup Y} {ι' : Q →* Y} {T : Subgroup Q} {Ω : Set (Subgroup Q)}
    {A' : Subgroup Q} {Bg : Subgroup Y} (hT : IsSylowIn 2 T ⊤)
    (hι' : Function.Injective ι') (hran : ι'.range = G) (hmapT : T.map ι' = T₀)
    (hτ : ∀ A : Subgroup Q, tA T A = T ⊓ centralizer (A : Set Q))
    (hA'Ω : A' ∈ Ω) (hA'T : A' ≤ T) (hA'e : IsElemAbelian 2 A')
    (hA'map : A'.map ι' = Bg)
    {K : Subgroup Y} (hKG : K ≤ G) (hcen : T₀ ⊓ centralizer (Bg : Set Y) ≤ K)
    (hcardK : Nat.card K = 3 * Nat.card (K ⊓ T₀ : Subgroup Y))
    (hNK : ¬ K ≤ Subgroup.normalizer ((K ⊓ T₀ : Subgroup Y) : Set Y))
    (hAO : ¬ Bg ≤ pCoreOf 2 K) (hsupK : K ⊔ T₀ = G) :
    genEi 1 T Ω ⊔ T = ⊤ := by
  set K' : Subgroup Q := K.comap ι' with hK'def
  have hK'map : K'.map ι' = K := Subgroup.map_comap_eq_self (hran ▸ hKG)
  have hmapTK : (T ⊓ K').map ι' = T₀ ⊓ K := by
    rw [Subgroup.map_inf_eq _ _ _ hι', hmapT, hK'map]
  have hmapTA : (tA T A').map ι' ≤ T₀ ⊓ centralizer (Bg : Set Y) :=
    map_tA_le_centralizer hmapT hA'map (hτ A')
  have hτ' : tA T A' ≤ T ⊓ K' := by
    refine le_inf ?_ ?_
    · rw [hτ A']
      exact inf_le_left
    · exact Subgroup.map_le_iff_le_comap.mp (hmapTA.trans hcen)
  have hcardKs : Nat.card K' = Nat.card K := by
    rw [← Subgroup.card_map_of_injective hι', hK'map]
  have hcardTK : Nat.card (T ⊓ K' : Subgroup Q) = Nat.card (T₀ ⊓ K : Subgroup Y) := by
    rw [← Subgroup.card_map_of_injective hι', hmapTK]
  have hcardK' : Nat.card K' = 3 * Nat.card (T ⊓ K' : Subgroup Q) := by
    calc Nat.card K' = Nat.card K := hcardKs
      _ = 3 * Nat.card (K ⊓ T₀ : Subgroup Y) := hcardK
      _ = 3 * Nat.card (T₀ ⊓ K : Subgroup Y) := by rw [inf_comm]
      _ = 3 * Nat.card (T ⊓ K' : Subgroup Q) := by rw [← hcardTK]
  have hrel : (T ⊓ K').relIndex K' = 3 := by
    have h := Subgroup.relIndex_mul_card (H := T ⊓ K') (K := K')
    rw [inf_eq_left.mpr inf_le_right, hcardK'] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hSyl : IsSylowIn 2 (T ⊓ K') K' :=
    ⟨inf_le_right, hT.isPGroup.to_le inf_le_left, by rw [hrel]; norm_num⟩
  have hN : ¬ K' ≤ Subgroup.normalizer ((T ⊓ K' : Subgroup Q) : Set Q) := by
    intro hle
    apply hNK
    intro k hk
    rw [← hK'map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    have hk'' : k' ∈ Subgroup.normalizer ((T ⊓ K' : Subgroup Q) : Set Q) := hle hk'
    have h := CFSG.LocalAnalysis.WeakClosure81.NFA6.mem_normalizer_map (ι := ι') hk''
    rwa [hmapTK, inf_comm] at h
  have hSylTwo : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K') K' :=
    ⟨hSyl.le, hSyl.isPGroup, by
      rw [show ((T ⊓ K').subgroupOf K').index = (T ⊓ K').relIndex K' from rfl, hrel]
      norm_num⟩
  obtain ⟨φ⟩ := CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hSylTwo hrel hN
  have hAO' : ¬ A' ≤ pCoreOf 2 K' := by
    intro hle
    apply hAO
    have h := Subgroup.map_mono (f := ι') hle
    rwa [hA'map, CFSG.LocalAnalysis.WeakClosure81.NFA6.pCoreOf_map hι' 2 K', hK'map] at h
  have hKi : InCalEi 1 T A' K' :=
    CFSG.LocalAnalysis.WeakClosure81.inCalEi_of_bar2_mulEquiv_perm_three hA'T hA'e le_rfl hτ'
      hSyl ⟨φ⟩ hAO'
  have hKle : K' ≤ genEi 1 T Ω :=
    CFSG.LocalAnalysis.WeakClosure81.le_genEi_of_inCalEi hA'Ω hA'T hKi
  have hK'T : K' ⊔ T = ⊤ := by
    apply Subgroup.map_injective hι'
    rw [Subgroup.map_sup, hK'map, hmapT, hsupK, ← MonoidHom.range_eq_map, hran]
  rw [eq_top_iff]
  calc (⊤ : Subgroup Q) = K' ⊔ T := hK'T.symm
    _ ≤ genEi 1 T Ω ⊔ T := sup_le_sup_right hKle T

private theorem genEi_sup_eq_top_of_five {Q Y : Type} [Group Q] [Finite Q] [Group Y] [Finite Y]
    {G T₀ : Subgroup Y} {ι' : Q →* Y} {T : Subgroup Q} {Ω : Set (Subgroup Q)}
    {A' : Subgroup Q} {Bg : Subgroup Y} (hT : IsSylowIn 2 T ⊤)
    (hι' : Function.Injective ι') (hran : ι'.range = G) (hmapT : T.map ι' = T₀)
    (hτ : ∀ A : Subgroup Q, tA T A = T ⊓ centralizer (A : Set Q))
    (hA'Ω : A' ∈ Ω) (hA'T : A' ≤ T) (hA'e : IsElemAbelian 2 A')
    (hA'map : A'.map ι' = Bg)
    {x : Y} (hxG : x ∈ G) (hox : orderOf x = 5)
    (hcen : T₀ ⊓ centralizer (Bg : Set Y) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set Y))
    (hcomm : ∃ b ∈ Bg, b * x ≠ x * b)
    (hsupx : Subgroup.zpowers x ⊔ T₀ = G) :
    genEi 1 T Ω ⊔ T = ⊤ := by
  rw [← hran] at hxG
  obtain ⟨x', rfl⟩ := hxG
  have hox' : orderOf x' = 5 := by
    rw [← orderOf_injective ι' hι' x', hox]
  set P : Subgroup Q := Subgroup.zpowers x' with hPdef
  have hP : IsPGroup 5 P := by
    rw [hPdef]
    exact IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers]; exact hox')
  have hcyc : IsCyclic ↥P := by
    change IsCyclic ↥(Subgroup.zpowers x')
    exact Subgroup.isCyclic_zpowers x'
  have hPmap : P.map ι' = Subgroup.zpowers (ι' x') := by
    rw [hPdef]
    exact MonoidHom.map_zpowers ι' x'
  have hmapTA : (tA T A').map ι' ≤ T₀ ⊓ centralizer (Bg : Set Y) :=
    map_tA_le_centralizer hmapT hA'map (hτ A')
  have hτP : tA T A' ≤ Subgroup.normalizer (P : Set Q) := by
    intro t ht
    apply CFSG.LocalAnalysis.WeakClosure81.NFA6.mem_normalizer_of_map hι'
    rw [hPmap]
    exact hcen (hmapTA (Subgroup.mem_map_of_mem ι' ht))
  have ha : ∃ a ∈ A', ¬ P ≤ Subgroup.centralizer ({a} : Set Q) := by
    obtain ⟨b, hbB, hbx⟩ := hcomm
    rw [← hA'map] at hbB
    obtain ⟨a, haA, rfl⟩ := hbB
    refine ⟨a, haA, ?_⟩
    intro hle
    have hxa : x' * a = a * x' :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_zpowers x'))
    apply hbx
    rw [← map_mul, ← map_mul, hxa]
  have hKi : InCalEi 1 T A' (P ⊔ tA T A') :=
    CFSG.LocalAnalysis.WeakClosure81.inCalEi_sup_tA_of_isCyclic (p := 5) (by norm_num)
      (by norm_num) hT hA'T hA'e le_rfl hP hcyc hτP ha
  have hKle : P ⊔ tA T A' ≤ genEi 1 T Ω :=
    CFSG.LocalAnalysis.WeakClosure81.le_genEi_of_inCalEi hA'Ω hA'T hKi
  have hPle : P ≤ genEi 1 T Ω := (le_sup_left : P ≤ P ⊔ tA T A').trans hKle
  have hPT : P ⊔ T = ⊤ := by
    apply Subgroup.map_injective hι'
    rw [Subgroup.map_sup, hPmap, hmapT, hsupx, ← MonoidHom.range_eq_map, hran]
  rw [eq_top_iff]
  calc (⊤ : Subgroup Q) = P ⊔ T := hPT.symm
    _ ≤ genEi 1 T Ω ⊔ T := sup_le_sup_right hPle T

theorem genEi_sup_eq_top_of_fourTenModel {Q Y : Type} [Group Q] [Finite Q] [Group Y] [Finite Y]
    {G T₀ : Subgroup Y} (hM : FourTenModel G T₀) (ι : Q →* Y) (hι : Function.Injective ι)
    (hrange : ι.range = G) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hτ : ∀ A : Subgroup Q, tA T A = T ⊓ centralizer (A : Set Q)) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) (h4 : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A) :
    genEi 1 T Ω ⊔ T = ⊤ := by
  obtain ⟨ι', hι', hran, hmapT⟩ :=
    CFSG.GroupTheory.exists_injective_map_eq_of_isSylowIn hM.sylow ι hι hrange hT
  obtain ⟨A, hAΩ, hAT⟩ := IsOmegaColl.exists_mem_le hT hΩ
  have hAe : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hA4 : 4 ≤ Nat.card A := h4 A hAΩ hAT
  set B : Subgroup Y := A.map ι' with hBdef
  have hBT : B ≤ T₀ := by
    rw [hBdef, ← hmapT]
    exact Subgroup.map_mono hAT
  have hBe : IsElemAbelian 2 B := by
    rw [hBdef]
    exact hAe.map ι'
  have hB4 : 4 ≤ Nat.card B := by
    rw [hBdef, Subgroup.card_map_of_injective hι']
    exact hA4
  obtain ⟨g, hgG, hBgT, hmem⟩ := hM.member B hBT hBe hB4
  rw [← hran] at hgG
  obtain ⟨g', rfl⟩ := hgG
  set A' : Subgroup Q := A.map (MulAut.conj g').toMonoidHom with hA'def
  have hA'map : A'.map ι' = B.map (MulAut.conj (ι' g')).toMonoidHom := by
    rw [hA'def, hBdef, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hA'Ω : A' ∈ Ω := by
    have h1 := hΩ.conj A hAΩ g'⁻¹
    rw [CFSG.Quasithin.conjSubgroup_eq_conjSub A g'⁻¹, inv_inv] at h1
    rwa [CFSG.Quasithin.A1b.conjSub, ← hA'def] at h1
  have hA'T : A' ≤ T := by
    refine (Subgroup.map_le_map_iff_of_injective hι').mp ?_
    rw [hA'map, hmapT]
    exact hBgT
  have hA'e : IsElemAbelian 2 A' := hAe.map (MulAut.conj g').toMonoidHom
  rcases hmem with ⟨K, hKG, hcen, hcardK, hNK, hAO, hsupK⟩ |
    ⟨x, hxG, hox, hcen, hcomm, hsupx⟩
  · exact genEi_sup_eq_top_of_sThree hT hι' hran hmapT hτ hA'Ω hA'T hA'e hA'map hKG hcen
      hcardK hNK hAO hsupK
  · exact genEi_sup_eq_top_of_five hT hι' hran hmapT hτ hA'Ω hA'T hA'e hA'map hxG hox hcen hcomm
      hsupx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
