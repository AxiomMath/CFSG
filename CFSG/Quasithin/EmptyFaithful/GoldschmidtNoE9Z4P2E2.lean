module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sp4B
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg2
public import CFSG.Quasithin.EmptyFaithful.S146zSWr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace E9P2.E2

section Out

variable {X : Type*} [Group X] {L : Subgroup X} [L.Normal]

theorem mem_of_conjNormal_mem_inner (hC : Subgroup.centralizer (L : Set X) = ⊥) {x : X}
    (hx : MulAut.conjNormal (H := L) x ∈ inner ↥L) : x ∈ L := by
  obtain ⟨l, hl⟩ := hx
  have h : (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun α : MulAut L => ((α ⟨y, hy⟩ : L) : X)) hl
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
    have h2 : (l : X) * y * (l : X)⁻¹ = x * y * x⁻¹ := h1
    calc y * ((l : X)⁻¹ * x) = (l : X)⁻¹ * ((l : X) * y * (l : X)⁻¹) * x := by group
      _ = (l : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
      _ = ((l : X)⁻¹ * x) * y := by group
  rw [hC, Subgroup.mem_bot] at h
  have : x = l := by
    calc x = (l : X) * ((l : X)⁻¹ * x) := by group
      _ = l := by rw [h, mul_one]
  exact this ▸ l.2

theorem isPGroup_two_quotient_of_out (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hout : IsPGroup 2 (Outer ↥L)) : IsPGroup 2 (X ⧸ L) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := hout (QuotientGroup.mk (MulAut.conjNormal (H := L) x))
  refine ⟨k, ?_⟩
  have h1 : MulAut.conjNormal (H := L) (x ^ 2 ^ k) ∈ inner ↥L := by
    rw [map_pow]
    exact (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hk)
  have hxL := mem_of_conjNormal_mem_inner hC h1
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hxL

end Out

section Sp4

variable {G : Type} [Group G] [Finite G]

theorem image_equiv_stated {G₁ K : Subgroup G} (hK : K ∈ cComp G₁) {F : Type} [Field F]
    [CharP F 2] (e : OTwoQuot K ≃* ↥(Matrix.symplecticGroup (Fin 2) F)) :
    Nonempty (↥(imageOTwoQuot G₁ K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK)
  exact ⟨(eK.symm.trans e).trans
    ((CFSG.QuasithinUnique.Lin2.Five.projEquivSymplectic F).symm.trans
      (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm)⟩

theorem isPGroup_two_outer_of_sp4 {L : Type*} [Group L] {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 4)
    (ψ₀ : L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) : IsPGroup 2 (Outer L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨-, hcard⟩ := CFSG.QuasithinUnique.Lin2.sp4OutCyclic F 2 hF' (by norm_num)
  have h4 : Nat.card (Outer L) = 2 ^ 2 := by
    rw [Nat.card_congr (equivalence (ψ₀.trans
      (CFSG.QuasithinUnique.Lin2.Five.projEquiv F))).toEquiv, hcard]
    norm_num
  exact IsPGroup.of_card h4

end Sp4

end E9P2.E2

section Case

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9_eq_sup_of_sp4 (h35 : Lemma1435) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p)
    (hKz : conjClosure (oTwoUpper H) (mcOf T) ∈ cComp (mcOf T))
    (e : Nonempty (OTwoQuot (conjClosure (oTwoUpper H) (mcOf T)) ≃*
      ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 2)))) :
    mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T := by
  classical
  obtain ⟨e⟩ := e
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape
  obtain ⟨ψ₀⟩ := E9P2.E2.image_equiv_stated hKz e
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by omega)]
    norm_num
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := le_of_mem_cComp hKz
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  have : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).Normal :=
    q_normal_image_of_normal hKzG (le_normalizer_conjClosure _ _)
  have hZ : ∀ n ∈ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)),
      (∀ m ∈ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)), n * m = m * n) →
        n = 1 := by
    intro n hn hnm
    have hc := CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv
      (ψ₀.trans (CFSG.QuasithinUnique.Lin2.Five.projEquiv (GaloisField 2 2)))
    have : (⟨n, hn⟩ : ↥(imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)))) ∈
        Subgroup.center _ :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hnm g g.2).symm
    rw [hc, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hE3 : ∃ E : Subgroup (OTwoQuot (mcOf T)),
      E ≤ imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 := by
    refine ⟨Eh, hloc.E_le_L, ⟨⟨⟨fun a b => ?_⟩⟩, hloc.exp_E⟩, ?_⟩
    · exact Subtype.ext (hloc.comm_E a a.2 b b.2)
    · rw [hloc.card_E]
      norm_num
  have hC := q_centralizer_eq_bot h36 hlist iS S hred hmax _ hZ hE3
    (fun h5 => absurd h5 (by have := hshape.1; omega))
  have hpq := E9P2.E2.isPGroup_two_quotient_of_out hC
    (E9P2.E2.isPGroup_two_outer_of_sp4 hcard ψ₀)
  exact le_antisymm (q_le_sup_of_isPGroup_quotient S hpq) (sup_le hKzG hTG)

theorem e9_caseE2 (h35 : Lemma1435) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ cComp (mcOf T)) (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁) {n : ℕ}
    (hn : 2 ≤ n) (_hne : Even n)
    (e : Nonempty (OTwoQuot K₁ ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 n)))) :
    Stage14614E9C2 T H := by
  classical
  have hshape' := hshape
  obtain rfl := hshape.1
  subst hKz
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape'
  obtain ⟨e⟩ := e
  obtain ⟨ψ₀⟩ := E9P2.E2.image_equiv_stated hK₁ e
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hn2 : n = 2 := hloc.sp4_eq_two hn hcard ψ₀ fun A hHA hA r hr hd =>
    e9_primes_of_solvable S hred hmax hshape' hHA hA r hr hd
  subst hn2
  exact ⟨hK₁, ⟨e⟩, e9_eq_sup_of_sp4 h35 h36 hlist iS S hred hmax hshape' hK₁ ⟨e⟩⟩

theorem e9_normalizer_le_of_E2 (h35 : Lemma1435) (_h36 : A36ForSQTK) (_hlist : SQTKList3Dvd)
    (_iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p) (hC : Stage14614E9C2 T H)
    {T0 : Subgroup G} (h1 : pCoreOf 2 H ≤ T0) (h2 : T0 ≤ T) :
    Subgroup.normalizer (T0 : Set G) ⊓ mcOf T ≤ H := by
  classical
  have hshape' := hshape
  obtain rfl := hshape.1
  obtain ⟨hKz, ⟨e⟩, hG⟩ := hC
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape'
  obtain ⟨ψ₀⟩ := E9P2.E2.image_equiv_stated hKz e
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by omega)]
    norm_num
  obtain ⟨hHU, -⟩ := hloc.sp4_normalizes (by omega) ψ₀
  obtain ⟨hNs, -⟩ := hloc.sp4_normalizer_data ⟨2, by rw [hcard]; norm_num⟩ ψ₀
  exact e9_normalizer_le_of_hat S hred h1 h2
    (hloc.normalizer_le (e9_hX_of_eq_sup S hG) hHU hNs
      (fun A hHA hA r hr hd => e9_primes_of_solvable S hred hmax hshape' hHA hA r hr hd)
      (fun P hPL hP3 => E9P2.Sp4.card_le_nine_of_sp4_four hcard ψ₀ hPL hP3)
      (q_image_mono h1) (q_image_mono h2))

end Case

end CFSG.Quasithin
