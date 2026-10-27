module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannL2Cyclic
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannOmegaZ
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannTransvection
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannL2Torus
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

private theorem sbl2triv_pCore_quotient {Y : Type*} [Group Y] :
    CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  set N : Subgroup Y := CFSG.pCore 2 Y with hN
  set K : Subgroup Y := (CFSG.pCore 2 (Y ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := Y ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := Y) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

private theorem sbl2triv_exists_pow_mem {Y : Type*} [Group Y] [Finite Y] (y : Y) :
    ∃ a : ℕ, y ^ 2 ^ a ∈ oResidual 2 Y := by
  obtain ⟨a, m, hm, hmn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨a, Subgroup.subset_closure ?_⟩
  have hdvd : orderOf (y ^ 2 ^ a) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hmn, pow_orderOf_eq_one])
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hm)

private theorem sbl2triv_eq_one_of_centralizes {Y : Type} [Group Y] [Finite Y]
    (hQ : CFSG.pCore 2 Y = ⊥) (hZ : Subgroup.center ↥(oResidual 2 Y) = ⊥) {c : Y}
    (hc : ∀ l ∈ oResidual 2 Y, l * c = c * l) : c = 1 := by
  haveI : (oResidual 2 Y).Normal := Stage1.Thm6.Prod.oResidual_normal 2 Y
  have hCn : (Subgroup.centralizer (oResidual 2 Y : Set Y)).Normal := inferInstance
  have hCp : IsPGroup 2 ↥(Subgroup.centralizer (oResidual 2 Y : Set Y)) := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := sbl2triv_exists_pow_mem g
    refine ⟨a, Subtype.ext ?_⟩
    have hz : (⟨g ^ 2 ^ a, ha⟩ : ↥(oResidual 2 Y)) ∈ Subgroup.center ↥(oResidual 2 Y) := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact (Commute.pow_right (Subgroup.mem_centralizer_iff.1 hg (l : Y) l.2) (2 ^ a)).eq
    rw [hZ, Subgroup.mem_bot] at hz
    have hz1 : g ^ 2 ^ a = 1 := congrArg Subtype.val hz
    exact hz1
  have hle : Subgroup.centralizer (oResidual 2 Y : Set Y) ≤ CFSG.pCore 2 Y :=
    le_sSup ⟨hCn, hCp⟩
  have hmem := hle (Subgroup.mem_centralizer_iff.2 hc)
  rwa [hQ, Subgroup.mem_bot] at hmem

private theorem sbl2triv_center_sl2 (K : Type) [Field K] [CharP K 2] :
    Subgroup.center SL(2, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hr1 : r = 1 := by
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linear_combination this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

private theorem sbl2triv_exists_ne_zero_sq_ne_one {F : Type} [Field F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at h4
  omega

private theorem sbl2triv_isQuasisimple_sl2 {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) : CFSG.IsQuasisimple SL(2, F) := by
  obtain ⟨a, ha, hasq⟩ := sbl2triv_exists_ne_zero_sq_ne_one h4
  have hperf : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha hasq⟩
  have hs : IsSimpleGroup (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨hperf, hs, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(2, F) ⧸ Subgroup.center SL(2, F)) := ⟨⟨h⟩⟩
  have : Group.IsPerfect (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ ‹_›

private theorem sbl2triv_isQuasisimple {n : ℕ} (hn : 2 ≤ n) {G : Type} [Group G]
    (ψ : G ≃* SL(2, GaloisField 2 n)) : CFSG.IsQuasisimple G := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm (sbl2triv_isQuasisimple_sl2 h4)

private theorem sbl2triv_center_bot {n : ℕ} {G : Type} [Group G]
    (ψ : G ≃* SL(2, GaloisField 2 n)) : Subgroup.center G = ⊥ := by
  refine le_antisymm (fun z hz => ?_) bot_le
  have hz' : ψ z ∈ Subgroup.center SL(2, GaloisField 2 n) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [sbl2triv_center_sl2, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (ψ.injective (by rw [hz', map_one]))

private theorem sbl2triv_three_dvd_card {n : ℕ} (hn : 1 ≤ n) {G : Type} [Group G]
    (ψ : G ≃* SL(2, GaloisField 2 n)) : 3 ∣ Nat.card G := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rw [Nat.card_congr ψ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 n

private theorem sbl2triv_nonempty_equiv_sl2 {n : ℕ} (hn : 1 ≤ n) {G : Type} [Group G]
    (e : G ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) :
    Nonempty (G ≃* SL(2, GaloisField 2 n)) := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨σ⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 n) hcard
  exact ⟨e.trans σ.symm⟩

private theorem sbl2triv_omega_le_center {Y : Type*} [Group Y] (R : Subgroup Y) :
    CFSG.Quasithin.omegaOneCenterOf R ≤ CFSG.Quasithin.centerOf R :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

private theorem sbl2triv_omega_le {Y : Type*} [Group Y] (R : Subgroup Y) :
    CFSG.Quasithin.omegaOneCenterOf R ≤ R :=
  (Subgroup.closure_le R).mpr fun _ hx => hx.1.1

private theorem sbl2triv_omega_normal {Y : Type*} [Group Y] (R : Subgroup Y) [hR : R.Normal] :
    (CFSG.Quasithin.omegaOneCenterOf R).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    have hc : g * y * g⁻¹ ∈ Subgroup.centralizer (R : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R := by simpa using hR.conj_mem r hr g⁻¹
      have key := Subgroup.mem_centralizer_iff.mp hy.1.2 _ hr'
      calc r * (g * y * g⁻¹) = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by rw [key]
        _ = g * y * g⁻¹ * r := by group
    have hsq : (g * y * g⁻¹) ^ 2 = 1 := by
      calc (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := conj_pow
        _ = 1 := by rw [hy.2]; group
    exact Subgroup.subset_closure ⟨⟨hR.conj_mem y hy.1.1 g, hc⟩, hsq⟩
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih

private theorem sbl2triv_isElemAbelian_omega {Y : Type*} [Group Y] (R : Subgroup Y) :
    CFSG.Open.IsElemAbelian 2 (CFSG.Quasithin.omegaOneCenterOf R) := by
  have hle := sbl2triv_omega_le_center R
  have hcomm : ∀ x ∈ CFSG.Quasithin.omegaOneCenterOf R, ∀ y ∈ CFSG.Quasithin.omegaOneCenterOf R,
      x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hle hy).2 x (hle hx).1
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hcomm x hx y hy) 2, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem sbl2triv_pCore_le_centralizer :
    CFSG.pCore 2 X ≤ Subgroup.centralizer (W315 X : Set X) := by
  intro q hq'
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact ((Subgroup.mem_centralizer_iff.mp (sbl2triv_omega_le_center _ hw).2) q hq').symm

private theorem sbl2triv_centralizer_le_pCore
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hZ : Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) = ⊥)
    (hWL : ⁅W315 X, oResidual 2 X⁆ ≠ ⊥) :
    Subgroup.centralizer (W315 X : Set X) ≤ CFSG.pCore 2 X := by
  haveI hWn : (W315 X).Normal := sbl2triv_omega_normal (CFSG.pCore 2 X)
  haveI hCn : (Subgroup.centralizer (W315 X : Set X)).Normal := inferInstance
  have hQC := sbl2triv_pCore_le_centralizer (X := X)
  have hLC : ¬ oResidual 2 X ≤ Subgroup.centralizer (W315 X : Set X) := by
    intro h
    refine hWL ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  haveI hLbn : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).Normal :=
    Stage1.Thm6.Prod.oResidual_normal 2 _
  have hCb : ((Subgroup.centralizer (W315 X : Set X)).map
      (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    hCn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.component_normal_subgroup
      (K := oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⟨hq, hLbn.isSubnormal⟩ hCb with h | h
  · exfalso
    refine hLC ?_
    rw [oResidual, Subgroup.closure_le]
    intro x hx
    have hxL : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈ oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
      Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ x) hx)
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (h hxL)
    have hdx' : (d : X ⧸ CFSG.pCore 2 X) = x := hdx
    have h1 := Subgroup.mul_mem _ hd (hQC (QuotientGroup.eq.mp hdx'))
    simpa using h1
  · intro c hc
    rw [Subgroup.commutator_comm] at h
    have hDc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have h1 := sbl2triv_eq_one_of_centralizes (sbl2triv_pCore_quotient (Y := X)) hZ
      (Subgroup.mem_centralizer_iff.mp
        (hDc (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 X)) hc)))
    exact (QuotientGroup.eq_one_iff c).mp h1

private theorem sbl2triv_relIndex_inf_le_two {Y : Type} [Group Y] [Finite Y]
    {W Q S E : Subgroup Y} [W.Normal] (hW : CFSG.Open.IsElemAbelian 2 W) (hWQ : W ≤ Q)
    (hQS : Q ≤ S) (hQC : Q ≤ Subgroup.centralizer (W : Set Y))
    (hE : CFSG.Quasithin.IsMaxElemAbelian S E) (hEQ : (E ⊓ Q).relIndex E ≤ 2) :
    (W ⊓ E).relIndex W ≤ 2 := by
  obtain ⟨hES, hEe, hEmax⟩ := hE
  have hDW : ∀ d ∈ E ⊓ Q, ∀ w ∈ W, d * w = w * d := fun d hd w hw =>
    (Subgroup.mem_centralizer_iff.mp (hQC hd.2) w hw).symm
  have hB : CFSG.Open.IsElemAbelian 2 (E ⊓ Q ⊔ W) :=
    (hEe.mono inf_le_left).sup_of_commute hW hDW
  have hBS : E ⊓ Q ⊔ W ≤ S := sup_le (inf_le_left.trans hES) (hWQ.trans hQS)
  have hcard : Nat.card ↥(E ⊓ Q ⊔ W) ≤ Nat.card ↥E := hEmax _ hBS hB
  have h1 : W.relIndex (E ⊓ Q ⊔ W) * Nat.card ↥(W ⊓ (E ⊓ Q ⊔ W)) = Nat.card ↥(E ⊓ Q ⊔ W) :=
    Subgroup.relIndex_mul_card W _
  have h2 : W.relIndex (E ⊓ Q) * Nat.card ↥(W ⊓ (E ⊓ Q)) = Nat.card ↥(E ⊓ Q) :=
    Subgroup.relIndex_mul_card W _
  have h3 : (W ⊓ (E ⊓ Q)).relIndex W * Nat.card ↥(W ⊓ (E ⊓ Q) ⊓ W) = Nat.card ↥W :=
    Subgroup.relIndex_mul_card _ W
  have h4 : (E ⊓ Q).relIndex E * Nat.card ↥(E ⊓ Q ⊓ E) = Nat.card ↥E :=
    Subgroup.relIndex_mul_card _ E
  have e1 : W ⊓ (E ⊓ Q ⊔ W) = W := inf_eq_left.mpr le_sup_right
  have e3 : W ⊓ (E ⊓ Q) ⊓ W = W ⊓ (E ⊓ Q) := inf_eq_left.mpr inf_le_left
  have e4 : E ⊓ Q ⊓ E = E ⊓ Q := inf_eq_left.mpr inf_le_left
  rw [e1, Subgroup.relIndex_sup_right] at h1
  rw [e3] at h3
  rw [e4] at h4
  have hd : 0 < Nat.card ↥(E ⊓ Q) := Nat.card_pos
  have key : (W ⊓ (E ⊓ Q)).relIndex W * Nat.card ↥(E ⊓ Q) ≤ 2 * Nat.card ↥(E ⊓ Q) := by
    calc (W ⊓ (E ⊓ Q)).relIndex W * Nat.card ↥(E ⊓ Q)
        = (W ⊓ (E ⊓ Q)).relIndex W * (W.relIndex (E ⊓ Q) * Nat.card ↥(W ⊓ (E ⊓ Q))) := by
          rw [h2]
      _ = W.relIndex (E ⊓ Q) * ((W ⊓ (E ⊓ Q)).relIndex W * Nat.card ↥(W ⊓ (E ⊓ Q))) := by ring
      _ = W.relIndex (E ⊓ Q) * Nat.card ↥W := by rw [h3]
      _ = Nat.card ↥(E ⊓ Q ⊔ W) := h1
      _ ≤ Nat.card ↥E := hcard
      _ = (E ⊓ Q).relIndex E * Nat.card ↥(E ⊓ Q) := h4.symm
      _ ≤ 2 * Nat.card ↥(E ⊓ Q) := Nat.mul_le_mul_right _ hEQ
  have hs := Nat.le_of_mul_le_mul_right key hd
  have hWD : W ⊓ (E ⊓ Q) = W ⊓ E := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hWQ h.1⟩⟩
  rw [hWD] at hs
  exact hs

private theorem sbl2triv_relIndex_conj {Y : Type*} [Group Y] (W : Subgroup Y) [hW : W.Normal]
    (t k : Y) :
    (W ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set Y)).relIndex W =
      (W ⊓ Subgroup.centralizer ({t} : Set Y)).relIndex W := by
  have h1 : (W ⊓ Subgroup.centralizer ({t} : Set Y)).map (MulAut.conj k).toMonoidHom =
      W ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set Y) := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨u, ⟨huW, hut⟩, rfl⟩
      refine ⟨hW.conj_mem u huW k, ?_⟩
      change k * u * k⁻¹ * (k * t * k⁻¹) = k * t * k⁻¹ * (k * u * k⁻¹)
      calc k * u * k⁻¹ * (k * t * k⁻¹) = k * (u * t) * k⁻¹ := by group
        _ = k * (t * u) * k⁻¹ := by rw [hut]
        _ = k * t * k⁻¹ * (k * u * k⁻¹) := by group
    · rintro ⟨hwW, hwt⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, ?_⟩, ?_⟩
      · simpa using hW.conj_mem w hwW k⁻¹
      · calc k⁻¹ * w * k * t = k⁻¹ * (w * (k * t * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * t * k⁻¹) * w) * k := by rw [hwt]
          _ = t * (k⁻¹ * w * k) := by group
      · change k * (k⁻¹ * w * k) * k⁻¹ = w
        group
  have h2 : W.map (MulAut.conj k).toMonoidHom = W := Subgroup.Normal.map_conj_eq W k
  calc (W ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set Y)).relIndex W
      = ((W ⊓ Subgroup.centralizer ({t} : Set Y)).map (MulAut.conj k).toMonoidHom).relIndex
          (W.map (MulAut.conj k).toMonoidHom) := by rw [h1, h2]
    _ = (W ⊓ Subgroup.centralizer ({t} : Set Y)).relIndex W :=
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k).injective

private theorem sbl2triv_exists_t {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    {S : Subgroup X} (hQS : CFSG.pCore 2 X ≤ S)
    (htriv : S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) = CFSG.pCore 2 X)
    (hJ : ¬ CFSG.Quasithin.thompsonJ S ≤ CFSG.pCore 2 X) :
    ∃ t : X, t ∈ S ∧ t ∉ oResidual 2 X ⊔ CFSG.pCore 2 X ∧ t ^ 2 = 1 ∧
      (W315 X ⊓ Subgroup.centralizer ({t} : Set X)).relIndex (W315 X) ≤ 2 := by
  haveI hWn : (W315 X).Normal := sbl2triv_omega_normal (CFSG.pCore 2 X)
  obtain ⟨E, hEmax, hEQ⟩ : ∃ E : Subgroup X, CFSG.Quasithin.IsMaxElemAbelian S E ∧
      ¬ E ≤ CFSG.pCore 2 X := by
    by_contra h
    push Not at h
    exact hJ (iSup₂_le h)
  obtain ⟨t, htE, htQ⟩ := IsConcreteLE.not_le_iff_exists.mp hEQ
  have htS : t ∈ S := hEmax.1 htE
  have hEL : E ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) ≤ CFSG.pCore 2 X := fun x hx => by
    have hx' : x ∈ S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) := ⟨hEmax.1 hx.1, hx.2⟩
    rwa [htriv] at hx'
  have hind := relIndex_le_two_of_typeL2 hn e hEmax.2.1 hEL
  have hW := sbl2triv_relIndex_inf_le_two (W := W315 X) (Q := CFSG.pCore 2 X) (S := S) (E := E)
    (sbl2triv_isElemAbelian_omega _) (sbl2triv_omega_le _) hQS sbl2triv_pCore_le_centralizer
    hEmax hind
  refine ⟨t, htS, fun htM => htQ ?_, hEmax.2.1.2 t htE, ?_⟩
  · have : t ∈ S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) := ⟨htS, htM⟩
    rwa [htriv] at this
  · have hle : W315 X ⊓ E ≤ W315 X ⊓ Subgroup.centralizer ({t} : Set X) := fun w hw =>
      ⟨hw.1, Subgroup.mem_centralizer_singleton_iff.mpr (hEmax.2.1.comm hw.2 htE)⟩
    exact (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans hW

private theorem sbl2triv_pow_of_sq_eq_one {Y : Type*} [Group Y] {t k : Y} (ht : t ^ 2 = 1)
    (h : (t * (k * t * k⁻¹)) ^ 12 = 1) : (t * k * t⁻¹ * k⁻¹) ^ 12 = 1 := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht)
  have h2 : t * k * t⁻¹ * k⁻¹ = t * (k * t * k⁻¹) := by
    rw [ht1]
    simp only [mul_assoc]
  rw [h2]
  exact h

private theorem sbl2triv_exists_order_three_mem {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (h3 : 3 ∣ Nat.card X) : ∃ a ∈ A, orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  by_contra hno
  push Not at hno
  have hA1 : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    by_contra ha1
    exact hno a ha (orderOf_eq_prime (hA.2 a ha) ha1)
  have hg3 : g ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  have hB : A ≤ Subgroup.zpowers g := by
    rw [hA1]
    exact bot_le
  have hgA := hAmax _ (CFSG.Open.isElemAbelian_zpowers hg3) hB
  have hg1 : g ∈ A := by
    rw [← hgA]
    exact Subgroup.mem_zpowers g
  rw [hA1, Subgroup.mem_bot] at hg1
  rw [hg1, orderOf_one] at hg
  omega

private theorem sbl2triv_main
    (hfalse : ∀ {Lb : Subgroup (X ⧸ CFSG.pCore 2 X)} [Lb.Normal] {n : ℕ}, 4 ≤ n → Even n →
      ∀ (_e : ↥Lb ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)),
        Subgroup.centralizer (Lb : Set (X ⧸ CFSG.pCore 2 X)) = ⊥ →
        ∀ {a t : X ⧸ CFSG.pCore 2 X}, a ∈ Lb → orderOf a = 3 → t ∉ Lb → t ^ 2 = 1 →
          t * a = a * t →
          (∀ k ∈ Lb, k * a = a * k → (t * k * t⁻¹ * k⁻¹) ^ 12 = 1) → False)
    (hF : generalizedFitting X = CFSG.pCore 2 X)
    {A S : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (htriv : S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) = CFSG.pCore 2 X) : Concl315 X S := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ψ⟩ := sbl2triv_nonempty_equiv_sl2 hn1 e
  have hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) :=
    sbl2triv_isQuasisimple hn2 ψ
  have hZ : Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) = ⊥ := sbl2triv_center_bot ψ
  have h3X : 3 ∣ Nat.card X := by
    have h1 := sbl2triv_three_dvd_card hn1 ψ
    have h2 : Nat.card ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ∣ Nat.card (X ⧸ CFSG.pCore 2 X) :=
      Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card (X ⧸ CFSG.pCore 2 X) ∣ Nat.card X :=
      Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))
    exact h1.trans (h2.trans h3)
  haveI hX : Nontrivial X := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3X
    refine ⟨⟨g, 1, fun h => ?_⟩⟩
    rw [h, orderOf_one] at hg
    omega
  by_cases hWL : ⁅W315 X, oResidual 2 X⁆ = ⊥
  · exact concl315_of_commutator_eq_bot hF hS hX hWL (sup_normal_of_typeL2 hn2 e S)
  have hQS : CFSG.pCore 2 X ≤ S := Push153.pCore_le_of_mem_maxInvariant hS
  by_cases hJ : CFSG.Quasithin.thompsonJ S ≤ CFSG.pCore 2 X
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
    have hQ1 : CFSG.pCore 2 X ≠ ⊥ := Push153.pCore_ne_bot_of_nontrivial hF
    have hS1 : S ≠ ⊥ := fun h => hQ1 (eq_bot_iff.mpr (hQS.trans h.le))
    exact Or.inl (Push153.exists_char_normal_of_thompsonJ_le hS2 hS1 hQS hJ)
  exfalso
  obtain ⟨t, htS, htM, ht2, htW⟩ := sbl2triv_exists_t hn2 e hQS htriv hJ
  obtain ⟨a, haA, ha3⟩ := sbl2triv_exists_order_three_mem hA hAmax h3X
  have hCQ := sbl2triv_centralizer_le_pCore hq hZ hWL
  haveI hWn : (W315 X).Normal := sbl2triv_omega_normal (CFSG.pCore 2 X)
  have hWnorm : ∀ g : X, g ∈ Subgroup.normalizer (W315 X : Set X) := fun g => by
    rw [Subgroup.normalizer_eq_top (W315 X)]
    exact Subgroup.mem_top g
  have hmap : (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    Stage1.Thm6.Prod.map_oResidual _ (QuotientGroup.mk'_surjective _) Nat.prime_two
  have hM : oResidual 2 X ⊔ CFSG.pCore 2 X =
      (oResidual 2 (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  haveI hLbn : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).Normal :=
    Stage1.Thm6.Prod.oResidual_normal 2 _
  haveI hMn : (oResidual 2 X ⊔ CFSG.pCore 2 X).Normal := by
    rw [hM]
    exact Subgroup.Normal.comap hLbn _
  have haL : a ∈ oResidual 2 X :=
    Subgroup.subset_closure (show Nat.Coprime (orderOf a) 2 by rw [ha3]; norm_num)
  have haM : a ∈ oResidual 2 X ⊔ CFSG.pCore 2 X := Subgroup.mem_sup_left haL
  have hat : a * t * a⁻¹ * t⁻¹ ∈ CFSG.pCore 2 X := by
    have h1 : a * t * a⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hS.prop.2.2 haA) t).mp htS
    have h2 : a * t * a⁻¹ * t⁻¹ ∈ S := S.mul_mem h1 (S.inv_mem htS)
    have h3 : a * t * a⁻¹ * t⁻¹ ∈ oResidual 2 X ⊔ CFSG.pCore 2 X := by
      have h4 : a * t * a⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by group
      rw [h4]
      exact Subgroup.mul_mem _ haM (hMn.conj_mem a⁻¹ (Subgroup.inv_mem _ haM) t)
    have h5 : a * t * a⁻¹ * t⁻¹ ∈ S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) := ⟨h2, h3⟩
    rwa [htriv] at h5
  have hbar_at : QuotientGroup.mk' (CFSG.pCore 2 X) t * QuotientGroup.mk' (CFSG.pCore 2 X) a =
      QuotientGroup.mk' (CFSG.pCore 2 X) a * QuotientGroup.mk' (CFSG.pCore 2 X) t := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) (a * t * a⁻¹ * t⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hat
    simp only [map_mul, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hbar_a3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) a) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : a ^ 3 = 1 := by
        have := pow_orderOf_eq_one a
        rwa [ha3] at this
      rw [this, map_one]
    · intro h1
      have haQ : a ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff a).mp h1
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := X) (p := 2)) ⟨a, haQ⟩
      have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [ha3] at hdvd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
  have hbar_aL : QuotientGroup.mk' (CFSG.pCore 2 X) a ∈ oResidual 2 (X ⧸ CFSG.pCore 2 X) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ haL
  have hbar_tL : QuotientGroup.mk' (CFSG.pCore 2 X) t ∉ oResidual 2 (X ⧸ CFSG.pCore 2 X) := by
    intro h
    apply htM
    rw [hM]
    exact Subgroup.mem_comap.mpr h
  have hbar_t2 : QuotientGroup.mk' (CFSG.pCore 2 X) t ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hC : Subgroup.centralizer
      (oResidual 2 (X ⧸ CFSG.pCore 2 X) : Set (X ⧸ CFSG.pCore 2 X)) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    exact sbl2triv_eq_one_of_centralizes (sbl2triv_pCore_quotient (Y := X)) hZ
      (Subgroup.mem_centralizer_iff.mp hc)
  refine hfalse (Lb := oResidual 2 (X ⧸ CFSG.pCore 2 X)) hn hev e hC hbar_aL hbar_a3 hbar_tL
    hbar_t2 hbar_at ?_
  intro k _ _
  obtain ⟨k0, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) k
  have h1 := pow_twelve_mem_centralizer (sbl2triv_isElemAbelian_omega (CFSG.pCore 2 X))
    (hWnorm t) (hWnorm (k0 * t * k0⁻¹)) htW
    (by rw [sbl2triv_relIndex_conj]; exact htW)
  have h2 := hCQ h1
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 X) ((t * (k0 * t * k0⁻¹)) ^ 12) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h2
  simp only [map_pow, map_mul, map_inv] at h3
  exact sbl2triv_pow_of_sq_eq_one hbar_t2 h3

theorem concl315_of_typeL2_trivial (hF : generalizedFitting X = CFSG.pCore 2 X)
    {A S : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (htriv : S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) = CFSG.pCore 2 X) : Concl315 X S :=
  sbl2triv_main false_of_commutator_pow_twelve hF hA hAmax hS hn hev e htriv

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
