module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Abs
public import CFSG.Quasithin.Recognition.St84.G24Vertex2ZBasis
public import CFSG.Quasithin.Recognition.St84.G24ModelFacts
public import CFSG.Quasithin.Recognition.St84.G24LinFacts
import CFSG.Quasithin.Recognition.St84.G24Vertex2Act
import CFSG.Quasithin.Recognition.St84.G24Vertex2Relations
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Mk

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open Certificates.A5GL42 (aN bN)
open CFSG.Quasithin.H.Q13 (om)
open CFSG.Quasithin.KGC31 (eElt)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

private theorem frame_Mk_normalize [Finite G]
    {L1 L2 S : Subgroup G} (F : G24Frame2 L1 L2 S) :
    ∃ F' : G24Frame2 L1 L2 S, F'.Mk = CFSG.Quasithin.St84.G24LE.omegaN := by
  have hspec := F.Mk_spec
  have h3 := hspec.2.2.1
  have h01 : (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ 1 := by decide
  rcases G24M.eq_zero_or_one_or_omegaN hspec.1 hspec.2.1 with h | h | h | h
  · exfalso
    rw [h] at h3
    have hzero : (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 3 = 0 := by
      simp [pow_succ]
    rw [hzero] at h3
    exact h01 h3
  · exfalso
    have hv : (Pi.single (0 : Fin 4) (1 : ZMod 2) : Fin 4 → ZMod 2) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simpa using this
    refine hv (hspec.2.2.2 _ ?_)
    rw [h]
    exact Matrix.one_mulVec _
  · exact ⟨F, h⟩
  · refine ⟨F.inv, ?_⟩
    rw [G24Frame2.Mk_inv, h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add,
      G24M.omegaN_pow_three, one_mul, pow_one]

section


theorem mem_B0_iff_of_mulEquiv (hM : G24M.Facts) {P S B : Subgroup G}
    {M : Subgroup G24M.Y}
    (hB : B = P ⊓ Subgroup.normalizer (S : Set G)) (hSP : S ≤ P) (hB0M : G24M.B0 ≤ M)
    (ψ : ↥P ≃* ↥M) (hψS : ∀ x : ↥P, (x : G) ∈ S ↔ ((ψ x : ↥M) : G24M.Y) ∈ G24M.T0)
    (x : ↥P) : (x : G) ∈ B ↔ ((ψ x : ↥M) : G24M.Y) ∈ G24M.B0 := by
  have hxP : (x : G) ∈ P := x.2
  rw [hB, Subgroup.mem_inf]
  have h1 : (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ x : ↥M) : G24M.Y) ∈ Subgroup.normalizer (G24M.T0 : Set G24M.Y) :=
    mem_normalizer_iff_of_mulEquiv ψ hSP (hM.T0_le_B0.trans hB0M) hψS x
  rw [h1, hM.normalizer_T0]
  exact ⟨fun h => h.2, fun h => ⟨hxP, h⟩⟩

theorem eq_Q1_or_eq_Q2_of_mulEquiv (hM : G24M.Facts) {P B N : Subgroup G}
    {M : Subgroup G24M.Y} (hB0M : G24M.B0 ≤ M) (ψ : ↥P ≃* ↥M) (hBP : B ≤ P)
    (hψB : ∀ x : ↥P, (x : G) ∈ B ↔ ((ψ x : ↥M) : G24M.Y) ∈ G24M.B0)
    (hNB : N ≤ B) (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hN : Nat.card N = 2 ^ 10) :
    (∀ x : ↥P, (x : G) ∈ N ↔ ((ψ x : ↥M) : G24M.Y) ∈ G24M.Q1) ∨
      (∀ x : ↥P, (x : G) ∈ N ↔ ((ψ x : ↥M) : G24M.Y) ∈ G24M.Q2) := by
  let f : ↥P →* G24M.Y := M.subtype.comp ψ.toMonoidHom
  have hf : Function.Injective f := M.subtype_injective.comp ψ.injective
  let N' : Subgroup G24M.Y := (N.subgroupOf P).map f
  have hN' : ∀ x : ↥P, (x : G) ∈ N ↔ ((ψ x : ↥M) : G24M.Y) ∈ N' := by
    intro x
    have h := Subgroup.mem_map_iff_mem (K := N.subgroupOf P) (f := f) hf (x := x)
    rw [show ((ψ x : ↥M) : G24M.Y) ∈ N' ↔ x ∈ N.subgroupOf P from h]
    exact (Subgroup.mem_subgroupOf).symm
  have hN'B0 : N' ≤ G24M.B0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (hψB x).mp (hNB (Subgroup.mem_subgroupOf.mp hx))
  have hB0N' : G24M.B0 ≤ Subgroup.normalizer (N' : Set G24M.Y) := by
    intro b hb
    let bP : ↥M := ⟨b, hB0M hb⟩
    let xP : ↥P := ψ.symm bP
    have hψx : (ψ xP : ↥M) = bP := ψ.apply_symm_apply bP
    have hxB : (xP : G) ∈ B := (hψB xP).mpr (by rw [hψx]; exact hb)
    have hxN : (xP : G) ∈ Subgroup.normalizer (N : Set G) := hBN hxB
    have h := (mem_normalizer_iff_of_mulEquiv ψ (hNB.trans hBP)
      (hN'B0.trans hB0M) hN' xP).mp hxN
    simpa [bP, hψx] using h
  have hcardN' : Nat.card N' = 2 ^ 10 := by
    show Nat.card ↥((N.subgroupOf P).map f) = 2 ^ 10
    rw [Subgroup.card_map_of_injective (f := f) hf]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNB.trans hBP)).toEquiv, hN]
  rcases hM.eq_Q1_or_eq_Q2 hN'B0 hB0N' hcardN' with h | h
  · left; intro x; rw [hN' x, h]
  · right; intro x; rw [hN' x, h]

private theorem psi_mem_bigB [Finite G] {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hD : G24LocalData L1 L2 S) (hM : G24M.Facts)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥G24M.M1)
    (hψ₁S : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.T0) :
    ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.B0 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hbigB1 : bigB L1 L2 S = (L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.normalizer (S : Set G) := by
    have h := F1.bigB_eq_parabolic_inf hR
    rwa [inf_eq_left.mpr hD.le_left] at h
  exact mem_B0_iff_of_mulEquiv hM hbigB1 (hD.le_left.trans le_sup_left) hM.B0_le_M1
    ψ₁ hψ₁S

private theorem psi_Q2_Z2 [Finite G] {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hD : G24LocalData L1 L2 S) (hM : G24M.Facts)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥G24M.M1)
    (hψ₁S : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.T0)
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ dsQ L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q1)
    (hψB : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.B0) :
    (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ dsQ L2 L1 S ↔
      ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q2) ∧
    (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ centerOf (dsQ L2 L1 S) ↔
      ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Z2) := by
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := dsQ L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2B : Q2 ≤ bigB L1 L2 S := by
    change dsQ L2 L1 S ≤ bigB L1 L2 S
    rw [dsQ_eq_pCoreOf_right]
    exact (F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic' hR)).trans
      le_sup_right
  have hbigBN : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 : Set G) :=
    le_sup_right.trans (P_le_normalizer_dsQ_right L1 L2 S)
  have hcase := eq_Q1_or_eq_Q2_of_mulEquiv hM hM.B0_le_M1 ψ₁ le_sup_right hψB hQ2B
    hbigBN hD.card_dsQ_right
  have hQ2 : ∀ x : ↥P1, (x : G) ∈ Q2 ↔
      ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q2 := by
    rcases hcase with h | h
    · exfalso
      have hQ2P1 : Q2 ≤ P1 := hQ2B.trans le_sup_right
      have hQ1P1 : Q1 ≤ P1 := dsQ_le_P_left L1 L2 S
      have heq : Q1 = Q2 := by
        apply le_antisymm
        · intro x hx
          exact (h ⟨x, hQ1P1 hx⟩).mpr ((hψ₁Q ⟨x, hQ1P1 hx⟩).mp hx)
        · intro x hx
          exact (hψ₁Q ⟨x, hQ2P1 hx⟩).mpr ((h ⟨x, hQ2P1 hx⟩).mp hx)
      exact hD.Q1_ne_Q2 heq
    · exact h
  refine ⟨hQ2, ?_⟩
  intro x
  exact CFSG.Quasithin.H13.Sec53F.mem_centerOf_iff_of_equiv ψ₁
    (hQ2B.trans le_sup_right)
    (hM.Q2_le_T0.trans (hM.T0_le_B0.trans hM.B0_le_M1)) hQ2 x

private theorem exists_k_data [Finite G] {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) (hM : G24M.Facts)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥G24M.M1)
    (hψ₁S : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.T0)
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ dsQ L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q1)
    (hψB : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.B0) :
    ∃ k : G, k ∈ bigB L1 L2 S ∧ orderOf k = 3 ∧ k ∉ L2 ∧
      (∀ x ∈ L2 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L2 L1 S) ∧
      (∀ z ∈ centerOf (dsQ L2 L1 S), k * z = z * k) ∧
      (dsQ L2 L1 S ⊓ Subgroup.centralizer ({k} : Set G) = centerOf (dsQ L2 L1 S)) ∧
      ∃ Y : Subgroup G, Y ≤ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
        Nat.card Y = 4 ∧ Y ⊓ centerOf (dsQ L2 L1 S) = ⊥ := by
  classical
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  obtain ⟨hQ2, hZ2⟩ := psi_Q2_Z2 hF hD hM ψ₁ hψ₁S hψ₁Q hψB
  have hQ2B : Q2 ≤ bigB L1 L2 S := by
    change dsQ L2 L1 S ≤ bigB L1 L2 S
    rw [dsQ_eq_pCoreOf_right]
    exact (F7.isSylowTwoOf_pCoreOf_le
      (F112W.isSylowTwoOf_parabolic'
        (Hyp111R.of_hyp111 rankOneListedFacts hF.1))).trans le_sup_right
  have hQ2P1 : Q2 ≤ P1 := hQ2B.trans le_sup_right
  obtain ⟨k, hkB, hk3, hkL, hkc⟩ := G24LocalData.exists_k_right hF h2 hD
  have hkP1 : k ∈ P1 := (le_sup_right : bigB L1 L2 S ≤ P1) hkB
  let kP : ↥P1 := ⟨k, hkP1⟩
  let y : G24M.Y := ((ψ₁ kP : ↥G24M.M1) : G24M.Y)
  have hyB : y ∈ G24M.B0 := (hψB kP).mp hkB
  have hy3 : orderOf y = 3 := by
    rw [show orderOf y = orderOf (ψ₁ kP) from Subgroup.orderOf_coe (ψ₁ kP),
      MulEquiv.orderOf_eq ψ₁ kP, Subgroup.orderOf_mk k hkP1, hk3]
  have hyc : ∀ b ∈ G24M.B0, ⁅y, b⁆ ∈ G24M.Q2 := by
    intro b hb
    let xP : ↥P1 := ψ₁.symm ⟨b, hM.B0_le_M1 hb⟩
    have hψx : (ψ₁ xP : ↥G24M.M1) = ⟨b, hM.B0_le_M1 hb⟩ := ψ₁.apply_symm_apply _
    have hxB : (xP : G) ∈ bigB L1 L2 S := (hψB xP).mpr (by rw [hψx]; exact hb)
    have hcomm : ⁅(kP : G), (xP : G)⁆ ∈ Q2 :=
      hkc (xP : G) ((le_sup_right : bigB L1 L2 S ≤ P2) hxB)
    let cP : ↥P1 := ⟨⁅(kP : G), (xP : G)⁆, hQ2P1 hcomm⟩
    have hmem : ((ψ₁ cP : ↥G24M.M1) : G24M.Y) ∈ G24M.Q2 := (hQ2 cP).mp hcomm
    have hcp : ((ψ₁ cP : ↥G24M.M1) : G24M.Y) = (ψ₁ ⁅kP, xP⁆ : G24M.Y) := rfl
    have hmap : ((ψ₁ cP : ↥G24M.M1) : G24M.Y) = ⁅y, b⁆ := by
      rw [hcp]
      let ψh : ↥P1 →* ↥G24M.M1 := ψ₁
      calc ((ψ₁ ⁅kP, xP⁆ : ↥G24M.M1) : G24M.Y)
          = ((ψh ⁅kP, xP⁆ : ↥G24M.M1) : G24M.Y) := rfl
        _ = ⁅((ψh kP : ↥G24M.M1) : G24M.Y), ((ψh xP : ↥G24M.M1) : G24M.Y)⁆ :=
              congrArg Subtype.val (map_commutatorElement ψh kP xP)
        _ = ⁅y, b⁆ := by
            have hx : ((ψh xP : ↥G24M.M1) : G24M.Y) = b := by
              show ((ψ₁ xP : ↥G24M.M1) : G24M.Y) = b
              rw [hψx]
            rw [hx]
            rfl
    rwa [hmap] at hmem
  obtain ⟨hyZ, hyQ, E, hE, hE4, hEZ⟩ := hM.central_mod_Q2 hyB hy3 hyc
  have hEM1 : E ≤ G24M.M1 := hE.trans (inf_le_left.trans hM.B0_le_M1)
  have hkZ : ∀ z ∈ Z2, k * z = z * k := by
    intro z hz
    let zP : ↥P1 := ⟨z, hQ2P1 ((inf_le_left : Z2 ≤ Q2) hz)⟩
    have hz2 : ((ψ₁ zP : ↥G24M.M1) : G24M.Y) ∈ G24M.Z2 := (hZ2 zP).mp hz
    have h := hyZ _ hz2
    have h' : ψ₁ (kP * zP) = ψ₁ (zP * kP) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    have h'' := congrArg Subtype.val (ψ₁.injective h')
    simpa using h''
  have hkQ : Q2 ⊓ Subgroup.centralizer ({k} : Set G) = Z2 := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.mp hz
      have hzk : k * z = z * k := Subgroup.mem_centralizer_iff.mp hzc k (by simp)
      let zP : ↥P1 := ⟨z, hQ2P1 hzQ⟩
      have hzQ' : ((ψ₁ zP : ↥G24M.M1) : G24M.Y) ∈ G24M.Q2 := (hQ2 zP).mp hzQ
      have hzkP : kP * zP = zP * kP := Subtype.ext hzk
      have hcomm : y * ((ψ₁ zP : ↥G24M.M1) : G24M.Y) =
          ((ψ₁ zP : ↥G24M.M1) : G24M.Y) * y := by
        have h1 : ψ₁ (kP * zP) = ψ₁ (zP * kP) := by rw [hzkP]
        rw [map_mul, map_mul] at h1
        exact congrArg Subtype.val h1
      have hmem : ((ψ₁ zP : ↥G24M.M1) : G24M.Y) ∈
          G24M.Q2 ⊓ Subgroup.centralizer ({y} : Set G24M.Y) := by
        refine Subgroup.mem_inf.mpr ⟨hzQ', ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hcomm
      rw [hyQ] at hmem
      exact (hZ2 zP).mpr hmem
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨(inf_le_left : Z2 ≤ Q2) hz, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hkZ z hz
  have hY : ∃ Y : Subgroup G,
      Y ≤ P2 ⊓ Subgroup.centralizer ({k} : Set G) ∧
        Nat.card Y = 4 ∧ Y ⊓ Z2 = ⊥ := by
    let E' : Subgroup ↥P1 := (E.subgroupOf G24M.M1).map ψ₁.symm.toMonoidHom
    let Y : Subgroup G := E'.map P1.subtype
    have hYcard : Nat.card Y = 4 := by
      show Nat.card ↥(((E.subgroupOf G24M.M1).map ψ₁.symm.toMonoidHom).map
        P1.subtype) = 4
      rw [Subgroup.card_map_of_injective (f := P1.subtype) P1.subtype_injective,
        Subgroup.card_map_of_injective (f := ψ₁.symm.toMonoidHom) ψ₁.symm.injective]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM1).toEquiv, hE4]
    have hYP2 : Y ≤ P2 := by
      intro x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx'
      have heE : ((e : ↥G24M.M1) : G24M.Y) ∈ E := Subgroup.mem_subgroupOf.mp he
      have heB : ((e : ↥G24M.M1) : G24M.Y) ∈ G24M.B0 := (hE heE).1
      have hxB : ((ψ₁.symm e : ↥P1) : G) ∈ bigB L1 L2 S :=
        (hψB (ψ₁.symm e)).mpr (by simpa using heB)
      exact (le_sup_right : bigB L1 L2 S ≤ P2) hxB
    have hYZ : Y ≤ Subgroup.centralizer ({k} : Set G) := by
      intro x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx'
      have heE : ((e : ↥G24M.M1) : G24M.Y) ∈ E := Subgroup.mem_subgroupOf.mp he
      have hec : ((e : ↥G24M.M1) : G24M.Y) ∈
          Subgroup.centralizer ({y} : Set G24M.Y) := (hE heE).2
      have hx'e : (ψ₁ (ψ₁.symm e) : ↥G24M.M1) = (e : ↥G24M.M1) :=
        ψ₁.apply_symm_apply e
      have hmodel : (ψ₁ (ψ₁.symm e) : ↥G24M.M1) * (ψ₁ kP) =
          (ψ₁ kP) * (ψ₁ (ψ₁.symm e)) := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hx'e]
        exact (Subgroup.mem_centralizer_iff.mp hec y (by simp)).symm
      have hpull : ψ₁ ((ψ₁.symm e) * kP) = ψ₁ (kP * (ψ₁.symm e)) := by
        rw [map_mul, map_mul]
        exact hmodel
      have h2 : ((ψ₁.symm e : ↥P1) : G) * k = k * ((ψ₁.symm e : ↥P1) : G) :=
        congrArg Subtype.val (ψ₁.injective hpull)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact h2.symm
    have hYZ2 : Y ⊓ Z2 = ⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      obtain ⟨hzY, hzZ⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hzY
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx'
      have heE : ((e : ↥G24M.M1) : G24M.Y) ∈ E := Subgroup.mem_subgroupOf.mp he
      have hzZ2 : ((e : ↥G24M.M1) : G24M.Y) ∈ G24M.Z2 := by
        have h := (hZ2 (ψ₁.symm e)).mp hzZ
        simpa using h
      have he1 : (e : ↥G24M.M1) = 1 := by
        have hmem : ((e : ↥G24M.M1) : G24M.Y) ∈ E ⊓ G24M.Z2 :=
          Subgroup.mem_inf.mpr ⟨heE, hzZ2⟩
        rw [hEZ] at hmem
        exact Subtype.ext (Subgroup.mem_bot.mp hmem)
      have hx1 : (ψ₁.symm e : ↥P1) = 1 := by
        rw [show e = (1 : ↥G24M.M1) from he1]
        simp
      have hxG : ((ψ₁.symm e : ↥P1) : G) = 1 := by rw [hx1]; rfl
      change ((ψ₁.symm e : ↥P1) : G) ∈ (⊥ : Subgroup G)
      rw [hxG]
      exact Subgroup.one_mem ⊥
    exact ⟨Y, fun x hx => Subgroup.mem_inf.mpr ⟨hYP2 hx, hYZ hx⟩, hYcard, hYZ2⟩
  exact ⟨k, hkB, hk3, hkL, hkc, hkZ, hkQ, hY⟩

theorem exists_g24Frame2_omegaN [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) (hM : G24M.Facts)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥G24M.M1)
    (hψ₁S : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.T0)
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ dsQ L1 L2 S ↔ ((ψ₁ x : ↥G24M.M1) : G24M.Y) ∈ G24M.Q1) :
    ∃ F : G24Frame2 L1 L2 S, F.Mk = CFSG.Quasithin.St84.G24LE.omegaN := by
  have hψB := psi_mem_bigB hF hD hM ψ₁ hψ₁S
  obtain ⟨k, hkB, hk3, hkL, hkc, hkZ, hkQ, hY⟩ :=
    exists_k_data hF h2 hD hM ψ₁ hψ₁S hψ₁Q hψB
  obtain ⟨F, -⟩ := exists_g24Frame2 hF h2 hD hkB hk3 hkL hkc hkZ hkQ hY
  exact frame_Mk_normalize F

end

theorem G24Frame2.exists_isAct_nonsplitX [Finite G]
    {L1 L2 S : Subgroup G} (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S)
    (hMk : F.Mk = CFSG.Quasithin.St84.G24LE.omegaN) :
    ∃ (u : G) (n : Fin 4 → G), u ∈ F.W ∧ u ∉ centerOf (dsQ L2 L1 S) ∧ F.IsNLift n ∧
      F.IsAct u n CFSG.Quasithin.St84.G24LE.nonsplitX := by
  classical
  obtain ⟨u, hu, hu'⟩ := F.exists_u hD
  obtain ⟨n, hn⟩ := F.exists_nLift
  obtain ⟨X, hX⟩ := F.exists_act hD hu hu' hn
  have hrel := F.isAct_relations hD hu hu' hn hX
  rw [hMk] at hrel
  obtain ⟨m, L, hL, hXL⟩ := G24M.ext2_solutions hrel.1 hrel.2.1 hrel.2.2.1
    hrel.2.2.2.1 hrel.2.2.2.2.1 hrel.2.2.2.2.2
  have hshift0 : CFSG.Quasithin.St84.G24LE.shiftX m 0 = m * aN + m := by
    simp [CFSG.Quasithin.St84.G24LE.shiftX]
  have hshift1 : CFSG.Quasithin.St84.G24LE.shiftX m 1 = m * bN + m := by
    simp [CFSG.Quasithin.St84.G24LE.shiftX]
  have hL0 : L ≠ 0 := by
    intro h0
    apply F.nonsplit hD hu hu' hn hX
    refine ⟨m, ?_, ?_⟩
    · have h := hXL 0
      rw [h0, Matrix.zero_mul, add_zero] at h
      rw [h, hshift0]
    · have h := hXL 1
      rw [h0, Matrix.zero_mul, add_zero] at h
      rw [h, hshift1]
  obtain ⟨r, hr3, hrL⟩ : ∃ r < 3, L = om ^ r := by
    rcases hL with h | h | h | h
    · exact absurd h hL0
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
    · exact ⟨2, by norm_num, by rw [h]⟩
  obtain ⟨huW, huZ, hX'⟩ := F.isAct_rescale hD hu hu' hn hX r
  let m' : Matrix (Fin 2) (Fin 4) (ZMod 2) := om ^ (2 * r) * m
  let X' : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2) := fun t => om ^ (2 * r) * X t
  have hX'act : F.IsAct (F.k ^ r * u * (F.k ^ r)⁻¹) n X' := hX'
  obtain ⟨hn', hX''⟩ := F.isAct_shift hD huW huZ hn hX'act m'
  have hsh0 : CFSG.Quasithin.St84.G24LE.shiftX m' 0 = m' * aN + m' := by
    simp [CFSG.Quasithin.St84.G24LE.shiftX]
  have hsh1 : CFSG.Quasithin.St84.G24LE.shiftX m' 1 = m' * bN + m' := by
    simp [CFSG.Quasithin.St84.G24LE.shiftX]
  have hsh2 : CFSG.Quasithin.St84.G24LE.shiftX m' 2 =
      m' * CFSG.Quasithin.St84.G24LE.omegaN + om * m' := by
    simp [CFSG.Quasithin.St84.G24LE.shiftX]
  have hmat : (![X' 0 + m' * aN + m', X' 1 + m' * bN + m',
      X' 2 + m' * F.Mk + om * m'] : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)) =
      CFSG.Quasithin.St84.G24LE.nonsplitX := by
    funext t
    fin_cases t
    · show om ^ (2 * r) * X 0 + m' * aN + m' = CFSG.Quasithin.St84.G24LE.nonsplitX 0
      rw [add_assoc, ← hsh0, hXL 0, hrL]
      exact G24M.ext2_normalize r m 0
    · show om ^ (2 * r) * X 1 + m' * bN + m' = CFSG.Quasithin.St84.G24LE.nonsplitX 1
      rw [add_assoc, ← hsh1, hXL 1, hrL]
      exact G24M.ext2_normalize r m 1
    · show om ^ (2 * r) * X 2 + m' * F.Mk + om * m' =
        CFSG.Quasithin.St84.G24LE.nonsplitX 2
      rw [hMk, add_assoc, ← hsh2, hXL 2, hrL]
      exact G24M.ext2_normalize r m 2
  rw [hmat] at hX''
  exact ⟨F.k ^ r * u * (F.k ^ r)⁻¹,
    fun j => n j * eElt ![F.k ^ r * u * (F.k ^ r)⁻¹,
      F.k * (F.k ^ r * u * (F.k ^ r)⁻¹) * F.k⁻¹] (fun s => m' s j),
    huW, huZ, hn', hX''⟩

end CFSG.Quasithin.F112R.St84

end
