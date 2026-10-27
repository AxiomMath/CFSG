module

public import CFSG.Quasithin.Recognition.Stroth.BenderFF
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.F112HypW

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G}

abbrev P1 (L1 L2 S : Subgroup G) : Subgroup G := L1 ⊔ bigB L1 L2 S

abbrev P2 (L1 L2 S : Subgroup G) : Subgroup G := L2 ⊔ bigB L1 L2 S

abbrev Q1 (L1 L2 S : Subgroup G) : Subgroup G := pCoreOf 2 (P1 L1 L2 S)

abbrev Q2 (L1 L2 S : Subgroup G) : Subgroup G := pCoreOf 2 (P2 L1 L2 S)

abbrev Z1 (L1 L2 S : Subgroup G) : Subgroup G := omegaOneCenterOf (Q1 L1 L2 S)

abbrev Z2 (L1 L2 S : Subgroup G) : Subgroup G := omegaOneCenterOf (Q2 L1 L2 S)

theorem pCoreOf_sup_pCoreOf (hF : Hyp111 L1 L2 S) :
    pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) = Q1 L1 L2 S := by
  set P := P1 L1 L2 S with hP
  set Q := Q1 L1 L2 S with hQ
  have hL1P : L1 ≤ P := le_sup_left
  have hQP : Q ≤ P := pCoreOf_le 2 P
  have hPP : P ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF)
  have hPN : P ≤ Subgroup.normalizer ((L1 ⊔ Q : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hPP (le_normalizer_pCoreOf 2 P)
  have hLQP : L1 ⊔ Q ≤ P := sup_le hL1P hQP
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 P
  have hQle : Q ≤ pCoreOf 2 (L1 ⊔ Q) :=
    le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le (hL1P.trans (le_normalizer_pCoreOf 2 P)) Subgroup.le_normalizer) hQ2
  refine le_antisymm ?_ hQle
  have hRle : pCoreOf 2 (L1 ⊔ Q) ≤ P := (pCoreOf_le 2 _).trans hLQP
  have hPR : P ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ Q) : Set G) :=
    hPN.trans (normalizer_le_normalizer_pCoreOf 2 (L1 ⊔ Q))
  exact le_pCoreOf_of_le_normalizer 2 hRle hPR (pCoreOf_isPGroup 2 (L1 ⊔ Q))

private theorem inf_pCoreOf_eq (hF : Hyp111 L1 L2 S) :
    Q1 L1 L2 S ⊓ L1 = pCoreOf 2 L1 := by
  refine le_antisymm ?_ (le_inf (Hyp111.pCoreOf_le_pCoreOf_vertex hF) (pCoreOf_le 2 L1))
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le inf_le_left)
  intro l hl
  exact CFSG.Quasithin.A4.mem_normalizer_inf
    ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hl)
    (Subgroup.le_normalizer hl)

noncomputable def oTwoQuotSupEquiv (hF : Hyp111 L1 L2 S) :
    oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* oTwoQuot ↥L1 := by
  classical
  set Q := Q1 L1 L2 S with hQ
  let Lhat : Subgroup G := L1 ⊔ Q
  let φ : ↥L1 →* oTwoQuot ↥Lhat :=
    (QuotientGroup.mk' (pCore 2 ↥Lhat)).comp (Subgroup.inclusion le_sup_left)
  have hQN : Q ≤ Subgroup.normalizer (L1 : Set G) :=
    (pCoreOf_le 2 (P1 L1 L2 S)).trans
      (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (H := L1) (K := Q) hQN).mp x.2
    refine ⟨⟨a, ha⟩, ?_⟩
    let y : ↥Lhat := ⟨a * b, Lhat.mul_mem
      ((le_sup_left : L1 ≤ L1 ⊔ Q) ha) ((le_sup_right : Q ≤ L1 ⊔ Q) hb)⟩
    have hx : x = y := Subtype.ext hab
    rw [hx]
    change QuotientGroup.mk (⟨a, (le_sup_left : L1 ≤ L1 ⊔ Q) ha⟩ : ↥Lhat) =
      QuotientGroup.mk y
    rw [QuotientGroup.eq]
    have hb' : (⟨a, (le_sup_left : L1 ≤ L1 ⊔ Q) ha⟩ : ↥Lhat)⁻¹ * y =
        ⟨b, (le_sup_right : Q ≤ L1 ⊔ Q) hb⟩ :=
      Subtype.ext (by simp [y])
    rw [hb', F1.mem_pCore_iff_coe]
    rwa [pCoreOf_sup_pCoreOf hF]
  have hker : pCore 2 ↥L1 = φ.ker := by
    ext l
    rw [MonoidHom.mem_ker]
    show l ∈ pCore 2 ↥L1 ↔ φ l = 1
    rw [show φ l = QuotientGroup.mk (⟨(l : G), (le_sup_left : L1 ≤ L1 ⊔ Q) l.2⟩ : ↥Lhat)
      from rfl]
    rw [QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe, F1.mem_pCore_iff_coe,
      pCoreOf_sup_pCoreOf hF, ← inf_pCoreOf_eq hF, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, l.2⟩⟩
  exact (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker).symm

theorem omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf
    (hF : Hyp111 L1 L2 S) : omegaOneCenterOf S ≤ Z1 L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hQS : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  change omegaOneOf (centerOf S) ≤ omegaOneOf (centerOf (Q1 L1 L2 S))
  refine Subgroup.closure_mono ?_
  rintro y ⟨hyZ, hy2⟩
  have hyS : y ∈ S := (Subgroup.mem_inf.mp hyZ).1
  have hyC : y ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hyZ).2
  have hyCentQ : y ∈ Subgroup.centralizer (Q1 L1 L2 S : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro q hq
    exact hyC q (hQS hq)
  have hyP : y ∈ P1 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hyS)
  have hchar : CharTwo (P1 L1 L2 S) := F1.parabolic_charTwo hR
  exact ⟨Subgroup.mem_inf.mpr ⟨hchar ⟨hyP, hyCentQ⟩, hyCentQ⟩, hy2⟩

theorem omegaOneCenterOf_ne_bot_of_hyp111 (hF : Hyp111 L1 L2 S) :
    omegaOneCenterOf S ≠ ⊥ := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hSne : S ≠ ⊥ := by
    intro hS
    apply hR.r1.borel_ne
    rw [hS, bot_inf_eq]
    have htop : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [htop, inf_top_eq]
  exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hF.h1.pgroup hSne

theorem omegaOneCenterOf_pCoreOf_eq (hF : Hyp111 L1 L2 S)
    (hS1 : S ≤ L1 ⊔ Q1 L1 L2 S)
    (h : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S = omegaOneCenterOf S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hQS : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  refine le_antisymm ?_ (omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf hF)
  intro x hx
  have hxQ : x ∈ Q1 L1 L2 S := (omegaOneCenterOf_le (Q1 L1 L2 S)) hx
  have hx2 : x ^ 2 = 1 := (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 x hx
  have hxS : x ∈ S := hQS hxQ
  have hxCentS : x ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (h (hS1 hs)) x hx).symm
  exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hxS, hxCentS⟩, hx2⟩

private theorem pCoreOf_right_le_of_isSylowTwoOf
    (hF : Hyp111 L1 L2 S) : Q2 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le
    (F112W.isSylowTwoOf_parabolic' (Hyp111R.of_hyp111 rankOneListedFacts hF))

theorem isSylowTwoOf_sup_pCoreOf
    (hF : Hyp111 L1 L2 S) (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) :
    IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := by
  have hP : IsSylowTwoOf S (P1 L1 L2 S) :=
    F112W.isSylowTwoOf_parabolic (Hyp111R.of_hyp111 rankOneListedFacts hF)
  have hSle : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hKle : L1 ⊔ Q1 L1 L2 S ≤ P1 L1 L2 S :=
    sup_le le_sup_left (pCoreOf_le 2 (P1 L1 L2 S))
  exact F7.isSylowTwoOf_mono_right hP hSle hKle

private theorem false_of_Z_eq_Z1_of_Z_eq_Z2
    (hF : Hyp111 L1 L2 S) (hZ1 : Z1 L1 L2 S = omegaOneCenterOf S)
    (hZ2 : Z2 L1 L2 S = omegaOneCenterOf S) : False := by
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (omegaOneCenterOf S : Set G) := by
    simpa [← hZ1] using
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (omegaOneCenterOf S : Set G) := by
    simpa [Z2, ← hZ2] using
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
        (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (omegaOneCenterOf S : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1N hP2N
  have hZleO : omegaOneCenterOf S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2
      ((omegaOneCenterOf_le S).trans le_sup_right) hG0N
      (hF.h1.pgroup.to_le (omegaOneCenterOf_le S))
  rw [hF.o2] at hZleO
  exact omegaOneCenterOf_ne_bot_of_hyp111 hF (le_bot_iff.mp hZleO)

private theorem exists_listed_sup
    (hF : Hyp111 L1 L2 S) (hL1 : VSzBig L1 ∨ VU3Big L1) :
    (∃ a : ℕ, 1 ≤ a ∧ Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* Sz a)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (2 ^ n) ^ 2 ∧
        (Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* StatedSU 3 (2 ^ n) F) ∨
          Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃*
            StatedProj (StatedSU 3 (2 ^ n) F)))) := by
  have he := oTwoQuotSupEquiv hF
  rcases hL1 with ⟨a, ha, ⟨e⟩⟩ | ⟨n, hn, F, hFld, hFin, hcard, heSU⟩
  · exact Or.inl ⟨a, ha, ⟨he.trans e⟩⟩
  · rcases heSU with h | h
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨n, hn, F, hFld, hFin, hcard, Or.inl ⟨he.trans e⟩⟩
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨n, hn, F, hFld, hFin, hcard, Or.inr ⟨he.trans e⟩⟩

private theorem false_of_le_centralizer_of_pCoreOf_le
    (hF : Hyp111 L1 L2 S) (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hQ : Q1 L1 L2 S ≤ Q2 L1 L2 S)
    (hZ : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) : False := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hSle : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hZeq : Z1 L1 L2 S = omegaOneCenterOf S := omegaOneCenterOf_pCoreOf_eq hF hSle hZ
  have hZle : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    rw [hZeq]
    have h' := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf
      (L1 := L2) (L2 := L1) (S := S) hF.symm
    simpa [Z1, Z2, Q1, Q2, P1, P2, bigB_comm] using h'
  by_cases hZ2 : Z2 L1 L2 S = Z1 L1 L2 S
  · exact false_of_Z_eq_Z1_of_Z_eq_Z2 hF hZeq (hZ2.trans hZeq)
  · obtain ⟨x, hxZ2, hxZ1⟩ :=
      SetLike.exists_of_lt (lt_of_le_of_ne hZle (Ne.symm hZ2))
    have hxCent2 : x ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) :=
      (Subgroup.mem_inf.mp ((Subgroup.closure_le (centerOf (Q2 L1 L2 S))).mpr
        (fun _ hx => hx.1) hxZ2)).2
    have hxQ2 : x ∈ Q2 L1 L2 S := (omegaOneCenterOf_le (Q2 L1 L2 S)) hxZ2
    have hxS : x ∈ S := pCoreOf_right_le_of_isSylowTwoOf hF hxQ2
    have hxP : x ∈ P1 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
        ((le_sup_right : S ≤ bigB L1 L2 S) hxS)
    have hxCent1 : x ∈ Subgroup.centralizer (Q1 L1 L2 S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact hxCent2 q (hQ hq)
    have hxQ1 : x ∈ Q1 L1 L2 S :=
      F1.parabolic_charTwo hR ⟨hxP, hxCent1⟩
    have hx2 : x ^ 2 = 1 :=
      (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 x hxZ2
    exact hxZ1 (Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hxQ1, hxCent1⟩, hx2⟩)

private theorem false_of_le_normalizer_of_pCoreOf_le
    (hF : Hyp111 L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hQ : Q1 L1 L2 S ≤ Q2 L1 L2 S)
    (hN : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G)) : False := by
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    sup_le ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S).trans hN)
      (hSB.trans (normalizer_le_normalizer_thompsonJ S))
  have hJ2 : IsPGroup 2 (thompsonJ S) := hF.h1.pgroup.to_le (thompsonJ_le_self S)
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S :=
    le_pCoreOf_of_le_normalizer 2
      ((thompsonJ_le_self S).trans
        ((le_sup_right : S ≤ bigB L1 L2 S).trans
          (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S))) hP1N hJ2
  have hQ2S : Q2 L1 L2 S ≤ S := pCoreOf_right_le_of_isSylowTwoOf hF
  have hJQ2 : thompsonJ S ≤ Q2 L1 L2 S := hJQ1.trans hQ
  have hJeq : thompsonJ S = thompsonJ (Q2 L1 L2 S) := thompsonJ_eq_of_le hJQ2 hQ2S
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    have hchar : ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_thompsonJ (Q2 L1 L2 S)
    have hmap : ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)).map
        (Q2 L1 L2 S).subtype = thompsonJ S := by
      rw [Subgroup.map_subgroupOf_eq_of_le (thompsonJ_le_self (Q2 L1 L2 S))]
      exact hJeq.symm
    have h := (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_map_of_characteristic
        ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)))
    rwa [hmap] at h
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1N hP2N
  have hJleO : thompsonJ S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2
      ((thompsonJ_le_self S).trans le_sup_right) hG0N hJ2
  rw [hF.o2] at hJleO
  have hSne : S ≠ ⊥ := by
    intro hS
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF
      (le_bot_iff.mp (by simpa [hS] using omegaOneCenterOf_le S))
  exact CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hF.h1.pgroup hSne
    (le_bot_iff.mp hJleO)

theorem not_pCoreOf_le_pCoreOf
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) (hL1 : VSzBig L1 ∨ VU3Big L1) :
    ¬ Q1 L1 L2 S ≤ Q2 L1 L2 S := by
  intro hQ
  have hHyp : Hyp111 L1 L2 S := hF.1
  have hSyl : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hHyp hS1
  have hdich := le_centralizer_or_le_normalizer_thompsonJ
    (exists_listed_sup hHyp hL1) hSyl
  rw [pCoreOf_sup_pCoreOf hHyp] at hdich
  rcases hdich with hZ | hN
  · exact false_of_le_centralizer_of_pCoreOf_le hHyp hS1 hQ hZ
  · exact false_of_le_normalizer_of_pCoreOf_le hHyp hSB hQ hN

private theorem le_normalizer_thompsonJ_of_not_le_centralizer
    (hF : Hyp111 L1 L2 S) (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hL1 : VSzBig L1 ∨ VU3Big L1)
    (hnot : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  have hSyl : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF hS1
  have hdich := le_centralizer_or_le_normalizer_thompsonJ
    (exists_listed_sup hF hL1) hSyl
  rw [pCoreOf_sup_pCoreOf hF] at hdich
  exact hdich.resolve_left hnot

end CFSG.Quasithin.Stroth

end
