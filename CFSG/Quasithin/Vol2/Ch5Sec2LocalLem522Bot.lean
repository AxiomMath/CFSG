module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalF11
public import CFSG.Quasithin.EmptyFaithful.S152He9Y2
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_le_of_isCyclic {D E : Subgroup G} (hD : IsCyclic ↥D) (hED : E ≤ D)
    {g : G} (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (E : Set G) := by
  have := hD
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ D := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgD]
    exact Subgroup.map_mono hED
  have hcard : Nat.card ((E.map (MulAut.conj g).toMonoidHom).subgroupOf D) =
      Nat.card (E.subgroupOf D) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h := (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hle, inf_eq_left.mpr hED] at h
  exact h

theorem mem_normalizer_sup_of_le_of_isCyclic {P D E Bo : Subgroup G} (hPB : P ≤ Bo)
    (hBP : Bo ≤ Subgroup.normalizer (P : Set G)) (hDP : D ⊔ P = Bo) (hD : IsCyclic ↥D)
    (hED : E ≤ D) {g : G} (hgB : g ∈ Subgroup.normalizer (Bo : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer ((P ⊔ E : Subgroup G) : Set G) := by
  have hDB : D ≤ Bo := hDP ▸ le_sup_left
  set N : Subgroup ↥Bo := P.subgroupOf Bo with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPB).mpr hBP
  set π := QuotientGroup.mk' N with hπ
  have hcyc : IsCyclic (↥Bo ⧸ N) := by
    have := hD
    refine isCyclic_of_surjective (π.comp (Subgroup.inclusion hDB)) ?_
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hb : (b : G) ∈ ((D ⊔ P : Subgroup G) : Set G) := by rw [hDP]; exact b.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D P (hDB.trans hBP)] at hb
    obtain ⟨d, hd, p, hp, hdp⟩ := hb
    refine ⟨⟨d, hd⟩, ?_⟩
    show π ⟨d, hDB hd⟩ = π b
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (⟨d, hDB hd⟩ : ↥Bo)⁻¹ * b = ⟨p, hPB hp⟩ := Subtype.ext (by simp [← hdp])
    rw [e]
    exact hp
  set Z := P ⊔ E with hZ
  have hEB : E ≤ Bo := hED.trans hDB
  have hZB : Z ≤ Bo := sup_le hPB hEB
  set Z' := Z.map (MulAut.conj g).toMonoidHom with hZ'
  have hZ'B : Z' ≤ Bo := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgB]
    exact Subgroup.map_mono hZB
  have hPZ' : P ≤ Z' := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hgP]
    exact Subgroup.map_mono le_sup_left
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hcomap : ∀ W : Subgroup G, P ≤ W →
      ((W.subgroupOf Bo).map π).comap π = W.subgroupOf Bo := by
    intro W hPW
    rw [Subgroup.comap_map_eq, hker, sup_eq_left]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hPW (Subgroup.mem_subgroupOf.mp hx))
  have hidx : ∀ W : Subgroup G, P ≤ W →
      ((W.subgroupOf Bo).map π).index = (W.subgroupOf Bo).index := by
    intro W hPW
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hcomap W hPW]
  have hcardZ : Nat.card (Z'.subgroupOf Bo) = Nat.card (Z.subgroupOf Bo) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'B).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hZ',
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hindex : (Z'.subgroupOf Bo).index = (Z.subgroupOf Bo).index := by
    have h1 := (Z'.subgroupOf Bo).card_mul_index
    have h2 := (Z.subgroupOf Bo).card_mul_index
    rw [hcardZ] at h1
    have hpos : 0 < Nat.card (Z.subgroupOf Bo) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have heq : (Z'.subgroupOf Bo).map π = (Z.subgroupOf Bo).map π :=
    (IsCyclic.subgroup_eq_iff_index_eq).mpr
      (by rw [hidx Z' hPZ', hidx Z le_sup_left, hindex])
  have h2 : Z'.subgroupOf Bo = Z.subgroupOf Bo := by
    rw [← hcomap Z' hPZ', heq, hcomap Z le_sup_left]
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hZ'B, inf_eq_left.mpr hZB] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

omit [Finite G] in
theorem le_normalizer_sup_of_le_of_le {X A C : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hC : X ≤ Subgroup.normalizer (C : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := fun g hg => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hC hg)]

theorem oTwoQuot_sup_iso_three {Y R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hYO : (pCoreOf 2 Y).relIndex Y = 3) (hOR : pCoreOf 2 Y ≤ R)
    (hnt : ∃ r ∈ R, ∃ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∉ pCoreOf 2 Y) :
    IsSylowTwoOf R (Y ⊔ R) ∧ R.relIndex (Y ⊔ R) = 3 ∧
      Nonempty (OTwoQuot (Y ⊔ R) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 Y with hP
  set Q := Y ⊔ R with hQ
  have hPY : P ≤ Y := pCoreOf_le 2 Y
  have hYQ : Y ≤ Q := le_sup_left
  have hRQ : R ≤ Q := le_sup_right
  set I := Y ⊓ R with hI
  have hIY : I ≤ Y := inf_le_left
  have hIR : I ≤ R := inf_le_right
  have hPI : P ≤ I := le_inf hPY hOR
  have h1 : Y.relIndex (R ⊔ Y) = Y.relIndex R := F1.relIndex_sup_eq_of_le_normalizer hRY
  rw [sup_comm] at h1
  have h2 : I.relIndex R = Y.relIndex R := Subgroup.inf_relIndex_right Y R
  have hm1 := Subgroup.relIndex_mul_relIndex I R Q hIR hRQ
  have hm2 := Subgroup.relIndex_mul_relIndex I Y Q hIY hYQ
  have hne : Y.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : R.relIndex Q = I.relIndex Y := by
    rw [h2, ← h1] at hm1
    have : Y.relIndex Q * R.relIndex Q = Y.relIndex Q * I.relIndex Y := by
      rw [hm1, mul_comm (Y.relIndex Q) (I.relIndex Y)]
      exact hm2.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this
  have h4 : I.relIndex Y ∣ 3 := by
    have := Subgroup.relIndex_mul_relIndex P I Y hPI hIY
    rw [hYO] at this
    exact Dvd.intro_left _ this
  have h5 : R.relIndex Q = 3 := by
    rw [h3]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h4 with h6 | h6
    · exfalso
      have hYI : Y ≤ I := Subgroup.relIndex_eq_one.mp h6
      have hYR : Y ≤ R := hYI.trans hIR
      have hYp : IsPGroup 2 Y := hR2.to_le hYR
      have hY2 : Y ≤ P := le_pCoreOf_of_le_normalizer le_rfl Subgroup.le_normalizer hYp
      have : P = Y := le_antisymm hPY hY2
      rw [this, Subgroup.relIndex_self] at hYO
      omega
    · exact h6
  have hsyl : IsSylowTwoOf R Q :=
    ⟨hRQ, hR2, by rw [show (R.subgroupOf Q).index = R.relIndex Q from rfl, h5]; norm_num⟩
  have hnn : ¬ Q ≤ Subgroup.normalizer (R : Set G) := by
    intro hQR
    obtain ⟨r, hr, y, hy, hnot⟩ := hnt
    apply hnot
    have hyQ : y ∈ Q := hYQ hy
    have hc1 : r * y * r⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRY hr) y).mp hy) (Y.inv_mem hy)
    have hc2 : r * y * r⁻¹ * y⁻¹ ∈ R := by
      have e : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
      rw [e]
      exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hQR hyQ) r⁻¹).mp (R.inv_mem hr))
    have hIN : Y ≤ Subgroup.normalizer (I : Set G) := by
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hQR (hYQ hg)⟩
    exact le_pCoreOf_of_le_normalizer hIY hIN (hR2.to_le hIR) ⟨hc1, hc2⟩
  obtain ⟨S, hS, hSi, hS1⟩ :=
    exists_isPGroup_index_quot_of_relIndex hRQ hR2 h5 (by norm_num) hnn
  exact ⟨hsyl, h5, nonempty_mulEquiv_perm_three
    (OTwoQuot.eq_bot_of_normal_of_isPGroup Q) hS hS1 hSi⟩

omit [Finite G] in
theorem borelOf_eq_of_relIndex_prime {Q R : Subgroup G} (hRQ : R ≤ Q) {p : ℕ} (hp : p.Prime)
    (hidx : R.relIndex Q = p) (hnn : ¬ Q ≤ Subgroup.normalizer (R : Set G)) :
    borelOf Q R = R := by
  have hinf : R ⊓ Q = R := inf_eq_left.mpr hRQ
  unfold borelOf
  rw [hinf]
  set Nn := Q ⊓ Subgroup.normalizer (R : Set G) with hNn
  have hRN : R ≤ Nn := le_inf hRQ Subgroup.le_normalizer
  have hNQ : Nn ≤ Q := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hRN hNQ
  rw [hidx] at hmul
  have hdvd : R.relIndex Nn ∣ p := Dvd.intro _ hmul
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h5
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hRN
  · exfalso
    rw [h5] at hmul
    have h1 : Nn.relIndex Q = 1 :=
      Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one p).symm)
    exact hnn ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)

end General

namespace Hyp5_2_2p

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}
  (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
include hyp

theorem prime_p : p.Prime := by
  rcases hyp.p_cases with rfl | rfl <;> norm_num

theorem Dp_inf_eq_bot {P : Subgroup G} (hP : IsPGroup 2 P) : Dp ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
  rw [hm, hyp.card_Dp]
  refine Nat.Coprime.pow_right m ?_
  rcases hyp.p_cases with rfl | rfl <;> norm_num

theorem S_facts (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    sec52S M H ≤ T ∧ T ≤ Subgroup.normalizer (sec52S M H : Set G) ∧
      B ≤ Subgroup.normalizer (sec52S M H : Set G) ∧
      sec52S M H ⊓ oTwoUpper H = T ⊓ oTwoUpper H ∧ sec52S M H ⊓ L = T ⊓ L ∧
      sec52S M H ⊓ L₂ = T ⊓ L₂ ∧ pCoreOf 2 M ≤ sec52S M H ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ sec52S M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨-, -, hBorel, -, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
  set S := sec52S M H with hSdef
  have hTMH : T ≤ M ⊓ H := le_inf h.T_le hH.1.1
  have hST : S ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hTMH)
  have hMHN : M ⊓ H ≤ Subgroup.normalizer (S : Set G) := le_normalizer_pCoreOf 2 _
  have hSK : S ⊓ oTwoUpper H = T ⊓ oTwoUpper H := hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hL₂K := hyp.choice.le_oTwoUpper
  have hSL₂ : S ⊓ L₂ = T ⊓ L₂ := by
    rw [← inf_eq_right.mpr hL₂K, ← inf_assoc, hSK, inf_assoc]
  have hO2le : ∀ X : Subgroup G, T ≤ X → M ⊓ H ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) →
      pCoreOf 2 X ≤ S := by
    intro X hTX hMHX
    have hXT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hTX)
    exact le_pCoreOf_of_le_normalizer 2 (hXT.trans hTMH) hMHX (pCoreOf_isPGroup 2 X)
  have hHMp : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  refine ⟨hST, hTMH.trans hMHN, hyp.notation59.1.1.trans hMHN, hSK, h.inf_L_eq h331 hR hH,
    hSL₂, hO2le M h.T_le (inf_le_left.trans (le_normalizer_pCoreOf 2 M)), ?_⟩
  exact hO2le _ (hH.1.1.trans hHMp) ((inf_le_right.trans hHMp).trans (le_normalizer_pCoreOf 2 _))

theorem isCyclic_D (hF : L2TorusFact) : IsCyclic ↥D :=
  (hyp.toHyp5_0_1.isCyclic_card_of_isHall hF hyp.notation59.2.1).1

theorem Dp_le_normalizer_inf : Dp ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  (hyp.Dp_le.trans hyp.notation59.2.1.1).trans inf_le_right

theorem T_le_normalizer_Y (hF : L2TorusFact) :
    T ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) := by
  have hh := hyp.toHyp5_0_1
  have hTL := hh.T_le_normalizer_inf
  have hTLN : T ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans hh.sup_le_normalizer
  intro t ht
  have hNN : t ∈ Subgroup.normalizer
      (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)).map
      (MulAut.conj t).toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq]
    congr 1
    exact congrArg (fun A : Subgroup G => (A : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL ht))
  have hB : t ∈ Subgroup.normalizer (borelL T L : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTLN ht, hNN⟩
  exact mem_normalizer_sup_of_le_of_isCyclic (le_inf inf_le_right Subgroup.le_normalizer)
    inf_le_right
    (hh.borelL_eq_sup hyp.notation59.2.1) (hyp.isCyclic_D hF) hyp.Dp_le hB (hTL ht)

theorem B_le_normalizer_Y (hF : L2TorusFact) (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) :
    B ≤ Subgroup.normalizer (((T ⊓ L) ⊔ Dp : Subgroup G) : Set G) := by
  have hh := hyp.toHyp5_0_1
  obtain ⟨-, -, hBS, -, hSL, -⟩ := hyp.S_facts h510 h331 hR
  have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
  have hBL : B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [← hSL]
    exact fun b hb =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hBS hb, hh.normal (hBM hb)⟩
  have hBD : B ≤ Subgroup.normalizer (Dp : Set G) := fun b hb =>
    mem_normalizer_of_le_of_isCyclic (hyp.isCyclic_D hF) hyp.Dp_le (hyp.notation59.2.2 hb)
  exact le_normalizer_sup_of_le_of_le hBL hBD

theorem relIndex_Y : (T ⊓ L).relIndex ((T ⊓ L) ⊔ Dp) = p := by
  have hh := hyp.toHyp5_0_1
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hyp.Dp_le_normalizer_inf
  rw [sup_comm] at h1
  rw [h1, ← Subgroup.inf_relIndex_right, inf_comm,
    hyp.Dp_inf_eq_bot (hh.sylow.1.to_le inf_le_left), Subgroup.relIndex_bot_left, hyp.card_Dp]

theorem pCoreOf_Y : pCoreOf 2 ((T ⊓ L) ⊔ Dp) = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  have hT2 : IsPGroup 2 ↥(T ⊓ L : Subgroup G) := hh.sylow.1.to_le inf_le_left
  have hZN : (T ⊓ L) ⊔ Dp ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hyp.Dp_le_normalizer_inf
  have hodd : ¬ 2 ∣ p := by rcases hyp.p_cases with rfl | rfl <;> norm_num
  have hsyl : IsSylowTwoOf (T ⊓ L) ((T ⊓ L) ⊔ Dp) :=
    ⟨le_sup_left, hT2, by
      show ¬ 2 ∣ (T ⊓ L).relIndex ((T ⊓ L) ⊔ Dp)
      rw [hyp.relIndex_Y]
      exact hodd⟩
  exact le_antisymm (F7.isSylowTwoOf_pCoreOf_le hsyl)
    (le_pCoreOf_of_le_normalizer 2 le_sup_left hZN hT2)

theorem Dp_not_le_normalizer (h311 : Theorem311Stmt) (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥) :
    ¬ Dp ≤ Subgroup.normalizer (sec52S M H : Set G) := by
  intro hDpS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  obtain ⟨hST, hTS, -, hSK, -, -, hOMS, -⟩ := hyp.S_facts h510 h331 hR
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hS1 : S ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
    exact le_bot_iff.mp (h0 ▸ hOMS)
  have hO' : pCoreOf 2 (Subgroup.normalizer (S : Set G)) ≠ ⊥ := by
    intro h0
    apply hS1
    have hle : S ≤ pCoreOf 2 (Subgroup.normalizer (S : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hS2
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hM₀ : InH T (Subgroup.normalizer (S : Set G)) := ⟨hTS, hO'⟩
  have hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
    obtain ⟨P, hP⟩ := exists_sylow_coe_eq hh.sylow
    have hstar : IsHStar (P : Subgroup G) M H := hP ▸ hyp.hStar
    have hTM : (P : Subgroup G) ≤ M := hP ▸ hh.T_le
    exact ⟨H ⊓ M, hP ▸ hstar.isUniqueMaxOver P hTM⟩
  have hTKn : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hTS' : IsSylowTwoOf T (oTwoUpper H ⊔ T) := hh.isSylowTwoOf le_sup_right
  have hRS : IsSylowTwoOf S (oTwoUpper H ⊔ S) :=
    isSylowTwoOf_sup_of_inf_le hST hTKn (by rw [inf_comm, ← hSK]; exact inf_le_left) hTS'
  obtain ⟨R₀, hR₀1, hR₀R, hR₀N⟩ := h311 G T hh.simple hh.nonabelian hh.qtke hh.sylow _ H S
    hM₀ hyp.hStar.1 hu hS1 hST hRS le_rfl
  apply hR₀1
  have hHN : H ≤ Subgroup.normalizer (R₀ : Set G) := le_sup_right.trans hR₀N
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hG₀N : Dp ⊔ (L₂ ⊔ S) ≤ Subgroup.normalizer (R₀ : Set G) :=
    sup_le (hDpS.trans (le_sup_left.trans hR₀N))
      (sup_le ((hyp.choice.le_oTwoUpper.trans (oTwoUpper_le H)).trans hHN) (hSH.trans hHN))
  have hle : R₀ ≤ pCoreOf 2 (Dp ⊔ (L₂ ⊔ S)) :=
    le_pCoreOf_of_le_normalizer 2 (hR₀R.trans (le_sup_right.trans le_sup_right)) hG₀N
      (hS2.to_le hR₀R)
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem sup_Y_eq (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    (T ⊓ L) ⊔ Dp ⊔ sec52S M H = Dp ⊔ sec52S M H := by
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts h510 h331 hR
  have hTLS : T ⊓ L ≤ sec52S M H := hSL ▸ inf_le_left
  apply le_antisymm
  · exact sup_le (sup_le (hTLS.trans le_sup_right) le_sup_left) le_sup_right
  · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem SDp_facts (hF : L2TorusFact) (h311 : Theorem311Stmt) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥) :
    IsSylowTwoOf (sec52S M H) (Dp ⊔ sec52S M H) ∧ (sec52S M H).relIndex (Dp ⊔ sec52S M H) = p ∧
      (p = 3 → Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* Equiv.Perm (Fin 3))) ∧
      (p = 5 → Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* DihedralGroup 5) ∨
        Nonempty (oTwoQuot ↥(Dp ⊔ sec52S M H) ≃* ↥(Sz 0))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec52S M H with hSdef
  set Y := (T ⊓ L) ⊔ Dp with hYdef
  obtain ⟨hST, hTS, -, -, hSL, -⟩ := hyp.S_facts h510 h331 hR
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hTLS : T ⊓ L ≤ S := hSL ▸ inf_le_left
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hST.trans (hyp.T_le_normalizer_Y hF)
  have hOY := hyp.pCoreOf_Y
  have hYidx : (pCoreOf 2 Y).relIndex Y = p := by rw [hOY]; exact hyp.relIndex_Y
  have hOS : pCoreOf 2 Y ≤ S := by rw [hOY]; exact hTLS
  have hnt : ∃ r ∈ S, ∃ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∉ pCoreOf 2 Y := by
    by_contra hcon
    push Not at hcon
    apply hyp.Dp_not_le_normalizer h311 h510 h331 hR hO
    intro d hd
    have hdY : d ∈ Y := Subgroup.mem_sup_right hd
    have hconj : ∀ d ∈ Y, ∀ x ∈ S, d * x * d⁻¹ ∈ S := by
      intro d hd x hx
      have h1 : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ ∈ S := hOS (hcon x⁻¹ (S.inv_mem hx) d hd)
      have h2 := S.mul_mem hx h1
      simpa [mul_assoc] using h2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj d hdY x hx, fun hx => ?_⟩
    have := hconj d⁻¹ (Y.inv_mem hdY) _ hx
    simpa [mul_assoc] using this
  have heq := hyp.sup_Y_eq h510 h331 hR
  rw [← hYdef] at heq
  rcases hyp.p_cases with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := oTwoQuot_sup_iso_three hS2 hSY hYidx hOS hnt
    rw [heq] at h1 h2 h3
    exact ⟨h1, h2, fun _ => h3, fun h => absurd h (by norm_num)⟩
  · obtain ⟨h1, h2, h3⟩ := He9.oTwoQuot_sup_iso hS2 hSY hYidx hOS hnt
    rw [heq] at h1 h2 h3
    exact ⟨h1, h2, fun h => absurd h (by norm_num), fun _ => h3⟩

theorem hyp111 (hF : L2TorusFact) (h311 : Theorem311Stmt) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2) (hLie : Stmt5_2_L2Lie)
    (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥) :
    Hyp111 L₂ (Dp ⊔ sec52S M H) (sec52S M H) ∧ borelOf (Dp ⊔ sec52S M H) (sec52S M H) =
      sec52S M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  have hN := hyp.notation59
  set S := sec52S M H with hSdef
  set Q₁ := Dp ⊔ S with hQ₁def
  obtain ⟨hST, hTS, hBS, -, hSL, hSL₂, hOMS, hOMpS⟩ := hyp.S_facts h510 h331 hR
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  obtain ⟨hsyl, hidx, h3, h5⟩ := hyp.SDp_facts hF h311 h510 h331 hR hO
  have hnn : ¬ Q₁ ≤ Subgroup.normalizer (S : Set G) := fun hle =>
    hyp.Dp_not_le_normalizer h311 h510 h331 hR hO (le_sup_left.trans hle)
  have hborQ : borelOf Q₁ S = S :=
    borelOf_eq_of_relIndex_prime le_sup_right hyp.prime_p hidx hnn
  obtain ⟨hlist, hbor, -⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  obtain ⟨hTL₂, -⟩ := hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have hL₂K := hyp.choice.le_oTwoUpper
  have hborL₂ : borelOf L₂ S = borelOf L₂ T := by
    unfold borelOf
    rw [hSL₂]
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  have hHMp : H ≤ Mp := le_normalizer_oTwoUpper H
  have hMchar : CharTwo M :=
    charTwo_of_inH' h.qtke h.sylow (inH_of_inM ⟨h.maxTwoLocal, h.T_le⟩)
  have hMpO : pCoreOf 2 Mp ≠ ⊥ := by
    intro h0
    apply hyp.toHyp5_1_8.pCoreOf_oTwoUpper_ne_bot
    have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 Mp :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans Subgroup.le_normalizer)
        (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)) (pCoreOf_isPGroup 2 _)
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hMpchar : CharTwo Mp := charTwo_of_inH' h.qtke h.sylow ⟨hH.1.1.trans hHMp, hMpO⟩
  obtain ⟨-, -, hBorel, hBhall, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf hH.1.1) (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hTKM : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK (inf_le_inf_right _ h.T_le) inf_le_right
  have hMKeq : B ⊔ (T ⊓ oTwoUpper H) = M ⊓ oTwoUpper H := sup_eq_of_isHall_isSylow hBhall hTKM
  have hQeq : (T ⊓ L) ⊔ Dp ⊔ S = Q₁ := hyp.sup_Y_eq h510 h331 hR
  have hTQ : T ≤ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hQeq]
    exact le_normalizer_sup_of_le_of_le (hyp.T_le_normalizer_Y hF) hTS
  have hBQ : B ≤ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hQeq]
    exact le_normalizer_sup_of_le_of_le (hyp.B_le_normalizer_Y hF h510 h331 hR) hBS
  have hMKQ : M ⊓ oTwoUpper H ≤ Subgroup.normalizer (Q₁ : Set G) := by
    rw [← hMKeq]
    exact sup_le hBQ (inf_le_left.trans hTQ)
  have hborL₂M : borelOf L₂ S ≤ M ⊓ oTwoUpper H := by
    rw [hborL₂]
    exact le_inf hbor (inf_le_left.trans hL₂K)
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hDpM : Dp ≤ M := hyp.Dp_le.trans (hN.2.1.1.trans (inf_le_left.trans h.L_le))
  have hc1 : CharTwo (L₂ ⊔ S ⊔ borelOf Q₁ S) := by
    rw [hborQ]
    refine charTwo_of_pCore_centralizer_le hMpchar ?_
      (inf_le_left.trans (hOMpS.trans (le_sup_right.trans le_sup_left)))
    exact sup_le (sup_le (hL₂K.trans Subgroup.le_normalizer) (hSH.trans hHMp)) (hSH.trans hHMp)
  have hc2 : CharTwo (Q₁ ⊔ S ⊔ borelOf L₂ S) := by
    refine charTwo_of_pCore_centralizer_le hMchar ?_
      (inf_le_left.trans (hOMS.trans (le_sup_right.trans le_sup_left)))
    exact sup_le (sup_le (sup_le hDpM hSM) hSM) (hborL₂M.trans inf_le_left)
  have hlistQ : IsRankOneListed (oTwoQuot ↥Q₁) := by
    rcases hyp.p_cases with hp | hp
    · obtain ⟨e⟩ := h3 hp
      exact isRankOneListed_perm_three e
    · rcases h5 hp with he | he
      · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
      · exact Or.inr (Or.inl ⟨0, he⟩)
  have hSQ : S ≤ Q₁ := le_sup_right
  have hSQeq : S ⊓ Q₁ = S := inf_eq_left.mpr hSQ
  refine ⟨⟨⟨inferInstance, hS2, hyp.S_le, by rw [hSL₂]; exact hTL₂, hlist, ?_, hc1⟩,
    ⟨inferInstance, hS2, hSQ.trans Subgroup.le_normalizer, by rw [hSQeq]; exact hsyl, hlistQ,
      hborL₂M.trans hMKQ, hc2⟩, ?_⟩, hborQ⟩
  · rw [hborQ]
    exact hyp.S_le
  · have e : L₂ ⊔ Q₁ ⊔ S = Dp ⊔ (L₂ ⊔ S) := by
      rw [hQ₁def]
      apply le_antisymm
      · exact sup_le (sup_le (le_sup_left.trans le_sup_right)
          (sup_le le_sup_left (le_sup_right.trans le_sup_right)))
          (le_sup_right.trans le_sup_right)
      · exact sup_le (le_sup_left.trans (le_sup_right.trans le_sup_left))
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    rw [e]
    exact hO

end Hyp5_2_2p

end CFSG.Quasithin.H13
