module

public import CFSG.Quasithin.H13.NQCoreCh1Statements
public import CFSG.Quasithin.Vol2.Ch1Nine

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma139Two : Lemma139Two := by
  intro G _ _ hQ hs hnab T X L hT hXF hL hXK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hXi, hXf⟩ := hXF
  set K : Subgroup G := conjClosure L T with hKdef
  have hLK : L ≤ K := fun z hz => by simpa using mem_conjClosure (T.one_mem) hz
  have hKLT : K ≤ L ⊔ T := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨t, ht, z, hz, rfl⟩
    exact mul_mem (mul_mem (mem_sup_right ht) (mem_sup_left hz)) (inv_mem (mem_sup_right ht)))
  have hTN : T ≤ normalizer (K : Set G) := le_normalizer_conjClosure L T
  have hLTN : L ⊔ T ≤ normalizer (K : Set G) := sup_le (hLK.trans le_normalizer) hTN
  have hKsub : IsSubnormal K (L ⊔ T) :=
    A4.subnormal_of_normal hKLT (Subgroup.normal_subgroupOf_of_le_normalizer hLTN)
  have hchar : CharTwo (L ⊔ T) := by
    obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
    have hH : InH (S : Subgroup G) (L ⊔ T) := ⟨hS ▸ le_sup_right, hL.2.2.2⟩
    exact charTwo_of_inH hQ.2.1 S hH
  have hKchar : CharTwo K := A4.charTwo_of_subnormal hKsub hchar
  have hLc := cComp_of_isLocal hL
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have hKperf : ⁅K, K⁆ = K := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) ?_
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have hLt : L.map (MulAut.conj t).toMonoidHom ≤ K := by
        rintro _ ⟨y, hy, rfl⟩
        exact mem_conjClosure ht hy
      have hLtp : ⁅L.map (MulAut.conj t).toMonoidHom, L.map (MulAut.conj t).toMonoidHom⁆ =
          L.map (MulAut.conj t).toMonoidHom := by
        rw [← Subgroup.map_commutator, hLperf]
      have hmem : t * z * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨z, hz, rfl⟩
      rw [← hLtp] at hmem
      exact Subgroup.commutator_mono hLt hLt hmem
  have hKX : IsXClass K :=
    ⟨fun hb => ne_bot_of_mem_cComp hLc (le_bot_iff.mp (hb ▸ hLK)),
      eq_oTwoUpper_of_perfect hKperf, hKchar⟩
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hL.1, hL.2.2.1⟩
  have hTKsyl : IsSylowTwoOf (T ⊓ K) K := A312.isSylowTwoOf_inf_of_subnormal hKsub hTsyl
  have hKTK : K ⊔ (T ⊓ K) = K := sup_eq_left.mpr inf_le_right
  have hTKN : T ⊓ K ≤ normalizer (X : Set G) := inf_le_left.trans hXi.2.1
  have hA : A410Hyp X K (T ⊓ K) :=
    { xclass := hXf.1
      yclass := hKX
      xy := hXK
      normalizes := inf_le_right.trans le_normalizer
      sylowT := by rw [hKTK]; exact hTKsyl
      o2le := by
        rw [hKTK]
        exact le_inf (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTKsyl)
          ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTKsyl).trans hTKN)
      sylowNT := by
        rw [hKTK, inf_eq_left.mpr hTKN]
        exact A4.isSylowTwoOf_mono hTKsyl (le_inf inf_le_right hTKN) inf_le_left }
  have h2 := a4_10_2 hA
  rw [hKTK] at h2
  have hKf := a4_10_3 hA hXf
  refine ⟨h2, isFaithfulLocal_iff_isXf.mpr ⟨hL, isXClass_of_isLocal hQ hT hL, ?_⟩⟩
  have hLsub : IsSubnormal L K := A4.subnormal_of_le_of_le (subnormal_of_mem_cComp hLc) hLK hKLT
  refine (a4_9 (isXClass_of_isLocal hQ hT hL) hLsub).mp fun hbot => hKf.2 ?_
  set Z₀ : Subgroup G := omegaOneCenterOf (pCoreOf 2 K) with hZ₀
  have hTZ : T ≤ normalizer (Z₀ : Set G) :=
    hTN.trans ((normalizer_le_normalizer_pCoreOf 2 K).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hLC : L ≤ centralizer (Z₀ : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have hKC : K ≤ centralizer (Z₀ : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro z hz
    have hz' : t⁻¹ * z * t ∈ Z₀ := by
      have := (mem_normalizer_iff.mp (hTZ (inv_mem ht)) z).mp hz
      simpa using this
    have hc : t⁻¹ * z * t * y = y * (t⁻¹ * z * t) := mem_centralizer_iff.mp (hLC hy) _ hz'
    calc z * (t * y * t⁻¹) = t * (t⁻¹ * z * t * y) * t⁻¹ := by group
      _ = t * (y * (t⁻¹ * z * t)) * t⁻¹ := by rw [hc]
      _ = t * y * t⁻¹ * z := by group
  show ⁅omegaOneCenterOf (pCoreOf 2 K), K⁆ = ⊥
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hKC)

end CFSG.Quasithin.H13.NQCore
