module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic2
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSt84HypA
public import CFSG.Literature.GL52Transport
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup
open CFSG.GH74.Uniqueness.Bender
open CFSG.Quasithin.H13.QRC
open CFSG.BenderSuzuki
open CFSG.GorensteinWalter
open CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem index_borelOf_of_l2 {L S : Subgroup G} {f : ℕ}
    (hf : 2 ≤ f) (hsyl : IsSylowTwoOf (S ⊓ L) L) (hL2 : IsL2Quot f (oTwoQuot ↥L)) :
    ((borelOf L S).subgroupOf L).index =
      Nat.card (((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) + 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  let T := ((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))
  have hTp : IsPGroup 2 T := hdata.1
  have hTodd : ¬ 2 ∣ T.index := hdata.2.1
  have hTcard : Nat.card T = 2 ^ f := by
    let Q : Sylow 2 (oTwoQuot ↥L) := hTp.toSylow hTodd
    have hQcoe : (Q : Subgroup (oTwoQuot ↥L)) = T := IsPGroup.toSylow_coe hTp hTodd
    obtain ⟨eL2⟩ := hL2
    have hBT : BenderType (oTwoQuot ↥L) f 1 1 := BenderType.linear f hf eL2
    obtain ⟨t, hc⟩ := hBT.exists_benderCore Q
    rw [← hQcoe, hc.card_eq, pow_one]
  rw [CFSG.Quasithin.F112R.St84.index_borelOf_of_psl2 (f := f) (by omega) hsyl hL2]
  change 2 ^ f + 1 = Nat.card T + 1
  rw [hTcard]

theorem mem_bigB_or_mem_doubleCoset_p2
    {L1 L2 S : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hF : F112HypW L1 L2 S)
    (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {g p : G} (hgL2 : g ∈ L2)
    (hgB : g ∉ bigB L1 L2 S) (hp : p ∈ P2 L1 L2 S) :
    p ∈ bigB L1 L2 S ∨
      p ∈ bigB L1 L2 S * ({g} : Set G) * bigB L1 L2 S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  let M := oTwoQuot ↥L2
  let π : ↥L2 →* M := QuotientGroup.mk' (pCore 2 ↥L2)
  let T : Subgroup M := ((S ⊓ L2).subgroupOf L2).map π
  let N : Subgroup M := ((borelOf L2 S).subgroupOf L2).map π
  have hdata := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  have hTp : IsPGroup 2 T := by simpa [T] using hdata.1
  have hTidx : ¬ 2 ∣ T.index := by simpa [T] using hdata.2.1
  have hNeq : N = Subgroup.normalizer (T : Set M) := by
    change Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L2)) ((borelOf L2 S).subgroupOf L2) =
      Subgroup.normalizer
        (Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L2)) ((S ⊓ L2).subgroupOf L2) :
          Set (oTwoQuot ↥L2))
    exact hdata.2.2
  have hker : π.ker ≤ (borelOf L2 S).subgroupOf L2 := by
    rw [show π.ker = pCore 2 ↥L2 from QuotientGroup.ker_mk' _]
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L2 := (CFSG.Quasithin.F1.mem_pCore_iff_coe x).mp hx
    exact CFSG.Quasithin.F1.sylow_le_borelOf L2 S
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow hx')
  let eM : M ≃* PSL2Model n := Classical.choice hL2
  let Q : Sylow 2 M := hTp.toSylow hTidx
  have hQcoe : (Q : Subgroup M) = T := IsPGroup.toSylow_coe hTp hTidx
  let U0 : Subgroup (PSL2Model n) := psl2UpperUnipotentSubgroup (GaloisField 2 n)
  have hcardK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hD0 : BenderData (PSL2Model n) U0 n := benderData_psl2 hcardK
  let Q0 : Sylow 2 (PSL2Model n) := hD0.isPGroup.toSylow hD0.not_dvd_index
  have hQ0coe : (Q0 : Subgroup (PSL2Model n)) = U0 :=
    IsPGroup.toSylow_coe hD0.isPGroup hD0.not_dvd_index
  let T' : Subgroup (PSL2Model n) := T.map eM.toMonoidHom
  have hT'p : IsPGroup 2 T' := hTp.map eM.toMonoidHom
  have hT'idx : ¬ 2 ∣ T'.index := by
    have h : T'.index = T.index := by
      simpa [T'] using Subgroup.index_map_equiv (H := T) eM
    rwa [h]
  let Qe : Sylow 2 (PSL2Model n) := hT'p.toSylow hT'idx
  have hQecoe : (Qe : Subgroup (PSL2Model n)) = T.map eM.toMonoidHom :=
    IsPGroup.toSylow_coe hT'p hT'idx
  obtain ⟨x, hx⟩ := CFSG.Literature.GL52.sylow_eq_map_conj Qe Q0
  have hD1 : BenderData (PSL2Model n) (Qe : Subgroup (PSL2Model n)) n := by
    have h := hD0.map (MulAut.conj x⁻¹)
    have hEq : Subgroup.map (MulAut.conj x⁻¹).toMonoidHom U0 =
        (Qe : Subgroup (PSL2Model n)) := by
      rw [← hQ0coe, hx, Subgroup.map_map]
      have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (PSL2Model n) := by
        ext y
        simp [MulAut.conj_apply]
      rw [hcomp, Subgroup.map_id]
    rwa [hEq] at h
  have hD2 : BenderData M T n := by
    have h := hD1.map eM.symm
    have hEq : Subgroup.map eM.symm.toMonoidHom
        (Subgroup.map eM.toMonoidHom T) = T := by
      rw [Subgroup.map_map]
      have hcomp : eM.symm.toMonoidHom.comp eM.toMonoidHom = MonoidHom.id M := by
        ext y
        simp
      rw [hcomp, Subgroup.map_id]
    rwa [hQecoe, hEq] at h
  have hNmap : N.index = ((borelOf L2 S).subgroupOf L2).index := by
    rw [show N = Subgroup.map π ((borelOf L2 S).subgroupOf L2) from rfl]
    exact Subgroup.index_map_eq ((borelOf L2 S).subgroupOf L2)
      (QuotientGroup.mk'_surjective _) hker
  have hidxT : (Subgroup.normalizer (T : Set M)).index = Nat.card T + 1 := by
    rw [← hNeq, hNmap]
    exact index_borelOf_of_l2 hn hF.1.h2.sylow hL2
  let y : M := π ⟨g, hgL2⟩
  have hyN : y ∉ N := by
    intro hy
    obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hy
    have hk' : b⁻¹ * ⟨g, hgL2⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbπ, inv_mul_cancel]
    have hmem : ⟨g, hgL2⟩ ∈ (borelOf L2 S).subgroupOf L2 := by
      have := (borelOf L2 S).subgroupOf L2 |>.mul_mem hb (hker hk')
      simpa using this
    exact hgB (by
      have := Subgroup.mem_subgroupOf.mp hmem
      exact (le_sup_right.trans le_sup_left : borelOf L2 S ≤ bigB L1 L2 S) this)
  have hyNorm : y ∉ Subgroup.normalizer (T : Set M) := by
    rwa [← hNeq]
  have hbru : ∀ z : M, z ∈ N ∨ ∃ n1 ∈ N, ∃ n2 ∈ N, z = n1 * y * n2 := by
    intro z
    have h := CFSG.Quasithin.Ch3E215M.bruhat_of_benderData hD2 hidxT hyNorm z
    rwa [← hNeq] at h
  have hL2decomp : ∀ z ∈ L2, z ∈ borelOf L2 S ∨
      ∃ m1 ∈ borelOf L2 S, ∃ m2 ∈ borelOf L2 S, z = m1 * g * m2 := by
    refine CFSG.Quasithin.Ch3E215M.bruhat_of_surjective (G₀ := G) (X := L2)
      (M := borelOf L2 S) (L := M) (g := g) hgL2 π hker ?_
    intro z
    simpa [N] using hbru z
  have hBnorm : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (CFSG.Quasithin.F1.bigB_le_normalizer_left hR).2
  have hB2leB : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hBnorm).mp hp
  rcases hL2decomp l hl with hlB | ⟨m1, hm1, m2, hm2, hl_eq⟩
  · exact Or.inl ((bigB L1 L2 S).mul_mem (hB2leB hlB) hb)
  · refine Or.inr ?_
    refine Set.mem_mul.mpr ⟨m1 * g, ?_, m2 * b,
      (bigB L1 L2 S).mul_mem (hB2leB hm2) hb, ?_⟩
    · exact Set.mem_mul.mpr ⟨m1, hB2leB hm1, g, by simp, rfl⟩
    · rw [hl_eq]
      group

theorem str83G4_commutator_x_conjugate_eq_bot
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S)
    (h : CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ⁅str83X L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆ = ⊥ := by
  classical
  let X := str83X L1 L2 S
  let W := CFSG.conjugate X d.w
  have hw2Q2 : d.w * d.w ∈ Q2 L1 L2 S := str83G4_w_mul_self_mem_q2 hfr d
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hQ2P1 : Q2 L1 L2 S ≤ P1 L1 L2 S :=
    hQ2S.trans ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hw2NX : d.w * d.w ∈ Subgroup.normalizer (X : Set G) :=
    le_normalizer_str83X L1 L2 S (hQ2P1 hw2Q2)
  have hWw : CFSG.conjugate W d.w = X := by
    change CFSG.conjugate (CFSG.conjugate X d.w) d.w = X
    rw [CFSG.conjugate_conjugate, CFSG.conjugate_eq_self_of_mem_normalizer hw2NX]
  have hXle : X ≤ CFSG.conjugate (Q1 L1 L2 S) d.w := by
    have h1 : CFSG.conjugate W d.w ≤ CFSG.conjugate (Q1 L1 L2 S) d.w :=
      Subgroup.map_mono h
    rwa [hWw] at h1
  have hZ1 : ⁅X, W⁆ ≤ Z1 L1 L2 S :=
    (Subgroup.commutator_mono le_rfl h).trans (str83G4_commutator_x_q1_le hfr)
  have hZ1w : ⁅X, W⁆ ≤ CFSG.conjugate (Z1 L1 L2 S) d.w := by
    calc ⁅X, W⁆ ≤ ⁅CFSG.conjugate (Q1 L1 L2 S) d.w, W⁆ :=
          Subgroup.commutator_mono hXle le_rfl
      _ = CFSG.conjugate ⁅Q1 L1 L2 S, X⁆ d.w := by
          simp only [CFSG.conjugate, W]
          exact (Subgroup.map_commutator _ _ _).symm
      _ = CFSG.conjugate ⁅X, Q1 L1 L2 S⁆ d.w := by rw [Subgroup.commutator_comm]
      _ ≤ CFSG.conjugate (Z1 L1 L2 S) d.w :=
          Subgroup.map_mono (str83G4_commutator_x_q1_le hfr)
  have hbot : ⁅X, W⁆ ≤ Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w :=
    le_inf hZ1 hZ1w
  rw [str83G4_z1_inf_conjugate_w hfr d] at hbot
  exact le_bot_iff.mp hbot

theorem str83G4_str83R_le_q1_iff
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    str83R L1 L2 S ≤ Q1 L1 L2 S ↔ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S := by
  classical
  have ha : 1 ≤ a := hfr.2.2.1
  have hR' : Hyp111R L2 L1 S := Hyp111R.symm (Hyp111R.of_hyp111 rankOneListedFacts hfr.1.1)
  have hlt : L2 ⊓ bigB L2 L1 S < L2 := by
    rw [CFSG.Quasithin.F1.inf_bigB_eq_borelOf hR']
    exact CFSG.Quasithin.F1.lt_borelOf hR'
  obtain ⟨g0, hg0L2, hg0B⟩ := SetLike.exists_of_lt hlt
  have hg0B' : g0 ∉ bigB L1 L2 S := fun h => hg0B ⟨hg0L2, by rwa [bigB_comm]⟩
  have hwP2 : d.w ∈ P2 L1 L2 S :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
  constructor
  · intro hR
    calc CFSG.conjugate (str83X L1 L2 S) d.w
        ≤ CFSG.conjugate (str83R L1 L2 S) d.w :=
          Subgroup.map_mono (le_conjClosure _ _)
      _ = str83R L1 L2 S :=
          CFSG.conjugate_eq_self_of_mem_normalizer (le_normalizer_str83R L1 L2 S hwP2)
      _ ≤ Q1 L1 L2 S := hR
  · intro hw
    have hmem : d.w ∈ bigB L1 L2 S ∨
        d.w ∈ bigB L1 L2 S * ({g0} : Set G) * bigB L1 L2 S :=
      mem_bigB_or_mem_doubleCoset_p2 (L1 := L1) (L2 := L2) (S := S) (n := 2 * a + 1)
        (by omega) hfr.1 hfr.2.2.2.2.1 hg0L2 hg0B' hwP2
    have hwBgB : d.w ∈ bigB L1 L2 S * ({g0} : Set G) * bigB L1 L2 S :=
      hmem.resolve_left (fun hwB => d.hwNotN (hfr.2.1 hwB))
    rw [Set.mem_mul] at hwBgB
    obtain ⟨x, hx, b3, hb3, hw_eq⟩ := hwBgB
    rw [Set.mem_mul] at hx
    obtain ⟨b1, hb1, g1, hg1, hx_eq⟩ := hx
    rw [Set.mem_singleton_iff] at hg1
    rw [hg1] at hx_eq
    have hw_eq' : d.w = b1 * g0 * b3 := by rw [← hw_eq, ← hx_eq]
    have hg0_eq : g0 = b1⁻¹ * d.w * b3⁻¹ := by rw [hw_eq']; group
    have hconj_le : ∀ p ∈ P2 L1 L2 S,
        CFSG.conjugate (str83X L1 L2 S) p ≤ Q1 L1 L2 S := by
      intro p hp
      have hpMem : p ∈ bigB L1 L2 S ∨
          p ∈ bigB L1 L2 S * ({g0} : Set G) * bigB L1 L2 S :=
        mem_bigB_or_mem_doubleCoset_p2 (L1 := L1) (L2 := L2) (S := S) (n := 2 * a + 1)
          (by omega) hfr.1 hfr.2.2.2.2.1 hg0L2 hg0B' hp
      rcases hpMem with hpB | hpBgB
      · have hXp : CFSG.conjugate (str83X L1 L2 S) p = str83X L1 L2 S :=
          CFSG.conjugate_eq_self_of_mem_normalizer
            (le_normalizer_str83X L1 L2 S ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hpB))
        rw [hXp]
        exact str83X_le_q1 hfr
      · rw [Set.mem_mul] at hpBgB
        obtain ⟨y, hy, c3, hc3, hp_eq⟩ := hpBgB
        rw [Set.mem_mul] at hy
        obtain ⟨c1, hc1, g1, hg1, hy_eq⟩ := hy
        rw [Set.mem_singleton_iff] at hg1
        rw [hg1] at hy_eq
        have hp_eq' : p = (c1 * b1⁻¹) * d.w * (b3⁻¹ * c3) := by
          calc p = c1 * g0 * c3 := by rw [← hp_eq, hy_eq]
            _ = (c1 * b1⁻¹) * d.w * (b3⁻¹ * c3) := by rw [hg0_eq]; group
        have hleftB : c1 * b1⁻¹ ∈ bigB L1 L2 S :=
          (bigB L1 L2 S).mul_mem hc1 ((bigB L1 L2 S).inv_mem hb1)
        have hrightB : b3⁻¹ * c3 ∈ bigB L1 L2 S :=
          (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb3) hc3
        have hXleft : CFSG.conjugate (str83X L1 L2 S) (c1 * b1⁻¹) =
            str83X L1 L2 S :=
          CFSG.conjugate_eq_self_of_mem_normalizer
            (le_normalizer_str83X L1 L2 S
              ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hleftB))
        have hQright : CFSG.conjugate (Q1 L1 L2 S) (b3⁻¹ * c3) = Q1 L1 L2 S :=
          CFSG.conjugate_eq_self_of_mem_normalizer
            ((le_normalizer_pCoreOf 2 (P1 L1 L2 S))
              ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hrightB))
        calc CFSG.conjugate (str83X L1 L2 S) p
            = CFSG.conjugate
                (CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) (c1 * b1⁻¹)) d.w)
                (b3⁻¹ * c3) := by
              rw [hp_eq',
                ← CFSG.conjugate_conjugate (str83X L1 L2 S) ((c1 * b1⁻¹) * d.w)
                  (b3⁻¹ * c3),
                ← CFSG.conjugate_conjugate (str83X L1 L2 S) (c1 * b1⁻¹) d.w]
          _ = CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) (b3⁻¹ * c3) := by
              rw [hXleft]
          _ ≤ CFSG.conjugate (Q1 L1 L2 S) (b3⁻¹ * c3) := Subgroup.map_mono hw
          _ = Q1 L1 L2 S := hQright
    rw [str83R]
    refine CFSG.Quasithin.conjClosure_le ?_
    intro p hp z hz
    have hp' := hconj_le p⁻¹ ((P2 L1 L2 S).inv_mem hp)
    have hmem : p * z * p⁻¹ ∈ CFSG.conjugate (str83X L1 L2 S) p⁻¹ := by
      rw [CFSG.mem_conjugate_iff]
      simpa [mul_assoc] using hz
    exact hp' hmem

end CFSG.Quasithin.Stroth

end
