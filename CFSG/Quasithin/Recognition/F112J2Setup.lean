module

public import CFSG.Quasithin.Recognition.F112WAssembly
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Recognition.F112WLocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W

namespace F112J2

variable {G : Type*} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem relIndex_inf_eq_three {L S : Subgroup G} (hL : IsSylowTwoOf (S ⊓ L) L)
    (hperm : Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))) : (S ⊓ L).relIndex L = 3 := by
  have hOS : pCoreOf 2 L ≤ S ⊓ L := isSylowTwoOf_pCoreOf_le hL
  have h6 := relIndex_pCoreOf_eq_six hperm
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 L) (S ⊓ L) L hOS hL.1
  obtain ⟨k, hk⟩ := relIndex_eq_two_pow (Q := pCoreOf 2 L) hL.2.1
  have hodd := F7.isSylowTwoOf_odd_relIndex hL
  rw [h6, hk] at hmul
  generalize (S ⊓ L).relIndex L = m at hodd hmul ⊢
  rcases k with _ | _ | k
  · norm_num at hmul
    omega
  · norm_num at hmul
    omega
  · have h4 : (4 : ℕ) ∣ 6 := ⟨2 ^ k * m, by rw [← hmul]; ring⟩
    omega

theorem borelOf_eq_inf_of_perm3 {L S : Subgroup G} (hL : IsSylowTwoOf (S ⊓ L) L)
    (hperm : Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))) (hne : borelOf L S ≠ L) :
    borelOf L S = S ⊓ L := by
  have h3 := relIndex_inf_eq_three hL hperm
  have hSB : S ⊓ L ≤ borelOf L S := F1.sylow_le_borelOf L S
  have hBL : borelOf L S ≤ L := F1.borelOf_le L S
  have hmul := Subgroup.relIndex_mul_relIndex (S ⊓ L) (borelOf L S) L hSB hBL
  rw [h3] at hmul
  have hBne : (borelOf L S).relIndex L ≠ 1 := fun h1 =>
    hne (le_antisymm hBL (Subgroup.relIndex_eq_one.mp h1))
  have hdvd : (borelOf L S).relIndex L ∣ 3 :=
    ⟨(S ⊓ L).relIndex (borelOf L S), by rw [← hmul]; ring⟩
  have h3' : (borelOf L S).relIndex L = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hBne
    · exact h
  have h1 : (S ⊓ L).relIndex (borelOf L S) = 1 := by
    rw [h3'] at hmul
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSB

theorem isSylowTwoOf_L2S (h : Hyp111R L1 L2 S) : IsSylowTwoOf S (L2 ⊔ S) := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  exact F7.isSylowTwoOf_mono_right (isSylowTwoOf_parabolic' h) le_sup_right
    (sup_le le_sup_left (hSB.trans le_sup_right))

theorem isSylowTwoOf_K1S (h : Hyp111R L1 L2 S) : IsSylowTwoOf S (L1 ⊔ S) := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  exact F7.isSylowTwoOf_mono_right (isSylowTwoOf_parabolic h) le_sup_right
    (sup_le le_sup_left (hSB.trans le_sup_right))

theorem charTwo_of_le_of_pCoreOf_le {P P' : Subgroup G} (hP : CharTwo P) (hle : P' ≤ P)
    (hO : pCoreOf 2 P ≤ P') : CharTwo P' := by
  rintro x ⟨hxP', hxC⟩
  have h1 : pCoreOf 2 P ≤ pCoreOf 2 P' :=
    le_pCoreOf_of_le_normalizer 2 hO (hle.trans (le_normalizer_pCoreOf 2 P)) (pCoreOf_isPGroup 2 P)
  have hxC' : x ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) := Subgroup.centralizer_le h1 hxC
  exact h1 (hP ⟨hle hxP', hxC'⟩)

theorem amalgamHyp_thesis (h : Hyp111R L1 L2 S) :
    AmalgamHyp (L1 ⊔ L2 ⊔ S) (L2 ⊔ S) (L1 ⊔ S) S where
  gen := le_antisymm
    (sup_le (sup_le (le_sup_of_le_right le_sup_left) (le_sup_of_le_left le_sup_left))
      (le_sup_of_le_left le_sup_right))
    (sup_le (sup_le ((le_sup_right : L2 ≤ L1 ⊔ L2).trans le_sup_left) le_sup_right)
      (sup_le ((le_sup_left : L1 ≤ L1 ⊔ L2).trans le_sup_left) le_sup_right))
  charTwo := by
    have hA := amalgamHyp_alpha h
    refine charTwo_of_le_of_pCoreOf_le hA.charTwo
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) ?_
    exact (isSylowTwoOf_pCoreOf_le hA.sylow₁).trans le_sup_right
  sylow₁ := isSylowTwoOf_L2S h
  sylow₂ := isSylowTwoOf_K1S h
  o2_trivial := h.hyp.o2

theorem inf_L2S_K1S (h : Hyp111R L1 L2 S)
    (hperm : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))) :
    (L2 ⊔ S) ⊓ (L1 ⊔ S) = S := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro x ⟨hx2, hx1⟩
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hL2P : L2 ⊔ S ≤ L2 ⊔ bigB L1 L2 S := sup_le le_sup_left (hSB.trans le_sup_right)
  have hL1P : L1 ⊔ S ≤ L1 ⊔ bigB L1 L2 S := sup_le le_sup_left (hSB.trans le_sup_right)
  have hxB : x ∈ bigB L1 L2 S := by
    rw [← F1.parabolic_inf_parabolic h]
    exact ⟨hL1P hx1, hL2P hx2⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes h.hyp.h2.normalizes).mp hx2
  have haB : a ∈ bigB L1 L2 S := by
    have := (bigB L1 L2 S).mul_mem hxB ((bigB L1 L2 S).inv_mem (hSB hb))
    simpa using this
  have haB2 : a ∈ borelOf L2 S := by
    have h' := F1.inf_bigB_eq_borelOf h.symm
    rw [bigB_comm] at h'
    rw [← h']
    exact ⟨ha, haB⟩
  have hne : borelOf L2 S ≠ L2 := h.r2.borel_ne
  rw [borelOf_eq_inf_of_perm3 h.hyp.h2.sylow hperm hne] at haB2
  exact S.mul_mem haB2.1 hb

theorem relIndex_L2S (h : Hyp111R L1 L2 S)
    (hperm : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))) :
    S.relIndex (L2 ⊔ S) = 3 := by
  rw [relIndex_sup_eq_relIndex_inf h.hyp.h2.normalizes, inf_comm]
  exact relIndex_inf_eq_three h.hyp.h2.sylow hperm

omit [Finite G] in
theorem conjClosure_sup_S {Z : Subgroup G} (hS : S ≤ Subgroup.normalizer (L2 : Set G))
    (hZ : S ≤ Subgroup.centralizer (Z : Set G)) :
    conjClosure Z (L2 ⊔ S) = conjClosure Z L2 := by
  refine le_antisymm (conjClosure_le fun x hx z hz => ?_) (conjClosure_mono le_rfl le_sup_left)
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hS).mp hx
  have hbz : b * z = z * b := (Subgroup.mem_centralizer_iff.mp (hZ hb) z hz).symm
  have e : a * b * z * (a * b)⁻¹ = a * z * a⁻¹ := by
    calc a * b * z * (a * b)⁻¹ = a * (b * z) * b⁻¹ * a⁻¹ := by group
      _ = a * (z * b) * b⁻¹ * a⁻¹ := by rw [hbz]
      _ = a * z * a⁻¹ := by group
  rw [e]
  exact mem_conjClosure ha hz

theorem amalgamHypV_thesis (h : Hyp111R L1 L2 S) {Z : Subgroup G}
    (hZS : Z ≤ quasithinOmegaOneCenter S)
    (hperm : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Z : Set G)) :
    AmalgamHypV (L1 ⊔ L2 ⊔ S) (L2 ⊔ S) (L1 ⊔ S) S (conjClosure Z (L2 ⊔ S)) := by
  have hA := amalgamHyp_thesis h
  set P : Subgroup G := L2 ⊔ S with hP
  have hSP : IsSylowTwoOf S P := hA.sylow₁
  have hF : P ⊓ Subgroup.centralizer (pCoreOf 2 P : Set G) ≤ pCoreOf 2 P := hA.charTwo
  have hZc : Z ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
    refine hZS.trans ?_
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  have hZcent : S ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp (hZc.trans inf_le_right)
  have hO2L : pCoreOf 2 L2 ≤ S := (isSylowTwoOf_pCoreOf_le h.hyp.h2.sylow).trans inf_le_left
  have hZO : pCoreOf 2 L2 ≤ Subgroup.centralizer (Z : Set G) := hO2L.trans hZcent
  have hSL2 : S ⊓ L2 ≤ Subgroup.normalizer (Z : Set G) :=
    inf_le_left.trans (hZcent.trans (Subgroup.centralizer_le_normalizer _))
  have hred : IsTwoReducedIn P (conjClosure Z P) :=
    isTwoReducedIn_conjClosure_of_sylowIn hSP.1 hSP.2.1 (F7.isSylowTwoOf_odd_relIndex hSP) hF hZS
  have hPN : P ≤ Subgroup.normalizer ((conjClosure Z P : Subgroup G) : Set G) := hred.2.1
  have hCV : L2 ⊓ Subgroup.centralizer (conjClosure Z P : Set G) ≤ pCoreOf 2 L2 := by
    refine le_trans ?_ (centralizer_conjClosure_le_pCoreOf hperm h.hyp.h2.sylow hSL2 hZO hZn)
    exact inf_le_inf_left L2 (Subgroup.centralizer_le (conjClosure_mono le_rfl le_sup_left))
  have hPL2 : P ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer h.hyp.h2.normalizes
  have hX : P ≤ Subgroup.normalizer ((S ⊔ L2 : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact Subgroup.le_normalizer
  have hCN : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (conjClosure Z P : Set G) ⊓ L2) := by
    refine (pCoreOf_isPGroup 2 L2).to_le ?_
    intro x hx
    exact hCV ⟨hx.2, hx.1.2⟩
  have hCP : P ⊓ Subgroup.centralizer (conjClosure Z P : Set G) ≤ P := inf_le_left
  have hCnorm : P ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (conjClosure Z P : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hPN.trans (normalizer_le_normalizer_centralizer _))
  have hT := inf_eq_pCoreOf_of_quotient hSP hCP hCnorm hPL2 hX hCN
  refine { toAmalgamHyp := hA, reduced := hred, cT := ?_ }
  rw [← hT, ← inf_assoc, inf_eq_left.mpr hSP.1]

theorem isNaturalS3_thesis (h : Hyp111R L1 L2 S) {Z : Subgroup G}
    (hZS : Z ≤ quasithinOmegaOneCenter S)
    (hperm : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Z : Set G))
    (hV4 : Nat.card ↥(conjClosure Z (L2 ⊔ S)) = 4) :
    IsNaturalS3 (L2 ⊔ S) (conjClosure Z (L2 ⊔ S)) := by
  have hyp := amalgamHypV_thesis h hZS hperm hZn
  set P : Subgroup G := L2 ⊔ S with hP
  set V : Subgroup G := conjClosure Z P with hVdef
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes
  have hZc : Z ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
    refine hZS.trans ?_
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  have hZcent : S ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp (hZc.trans inf_le_right)
  have hO2L : pCoreOf 2 L2 ≤ S := (isSylowTwoOf_pCoreOf_le h.hyp.h2.sylow).trans inf_le_left
  have hZO : pCoreOf 2 L2 ≤ Subgroup.centralizer (Z : Set G) := hO2L.trans hZcent
  have hSL2 : S ⊓ L2 ≤ Subgroup.normalizer (Z : Set G) :=
    inf_le_left.trans (hZcent.trans (Subgroup.centralizer_le_normalizer _))
  have hCV : L2 ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L2 := by
    refine le_trans ?_ (centralizer_conjClosure_le_pCoreOf hperm h.hyp.h2.sylow hSL2 hZO hZn)
    exact inf_le_inf_left L2 (Subgroup.centralizer_le (conjClosure_mono le_rfl le_sup_left))
  have hL2P : L2 ≤ P := le_sup_left
  have h6 : 6 ∣ Nat.card (autOn L2 V) := by
    rw [card_autOn_eq_relIndex (hL2P.trans hPN), ← relIndex_pCoreOf_eq_six hperm]
    exact Subgroup.relIndex_dvd_of_le_left L2 hCV
  have hdvd : Nat.card (autOn L2 V) ∣ Nat.card (autOn P V) :=
    Subgroup.card_dvd_of_le (autOn_le_autOn V hL2P)
  have hle : Nat.card (autOn P V) ≤ 6 := card_subgroup_mulAut_le_six hV4 _
  have hpos : 0 < Nat.card (autOn P V) := by
    rw [card_autOn_eq_relIndex hPN]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h6' : 6 ∣ Nat.card (autOn P V) := h6.trans hdvd
  have : Nat.card (autOn P V) = 6 := by
    obtain ⟨k, hk⟩ := h6'
    rcases k with _ | k
    · omega
    · omega
  refine ⟨hV4, ?_⟩
  rw [← card_autOn_eq_relIndex hPN]
  exact this

end F112J2

end CFSG.Quasithin
