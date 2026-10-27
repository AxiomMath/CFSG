module

public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShape
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDelete
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeA1
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeA2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeB1
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeB2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeM2
import CFSG.Mathlib.GroupTheory.CoprimeKernelLift
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType.NsQuot

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]
  {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

omit [Finite Q] in
theorem Datum.mem_img_L_iff (hD : Datum p N f L Bs Z) (s : ↥N) :
    f s ∈ img N f L ↔ (s : G) ∈ L := by
  constructor
  · intro hs
    obtain ⟨l, hl, hls⟩ := mem_img.mp hs
    have hk : s * l⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hls]
      exact mul_inv_cancel _
    have hsL : ((s * l⁻¹ : ↥N) : G) ∈ L := hD.ZL ((hD.mem_ker_iff _).mp hk)
    have h := L.mul_mem hsL hl
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using h
  · intro hs
    exact mem_img.mpr ⟨s, hs, rfl⟩

omit [Finite Q] in
theorem Datum.mem_centralizer_img_iff (hD : Datum p N f L Bs Z)
    (hL : Group.IsPerfect ↥L) (s : ↥N) :
    f s ∈ Subgroup.centralizer (img N f L : Set Q) ↔
      (s : G) ∈ Subgroup.centralizer (L : Set G) := by
  have : Group.IsPerfect ↥(L.subgroupOf N) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hD.LN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hD.LN).symm.surjective
  have hker : f.ker ≤ L.subgroupOf N := fun z hz => hD.ZL ((hD.mem_ker_iff z).mp hz)
  have hcent : ∀ z ∈ f.ker, ∀ l ∈ L.subgroupOf N, l * z = z * l := by
    intro z hz l hl
    exact Subtype.ext (hD.Zcent _ ((hD.mem_ker_iff z).mp hz) _ hl)
  constructor
  · intro hs
    have hcomm := CFSG.CoprimeKernel.commute_of_perfect
      (f := f) (L := L.subgroupOf N) inferInstance hker hcent (b := s) (by
        intro l hl
        exact ((Subgroup.mem_centralizer_iff.mp hs) (f l) (mem_img.mpr ⟨l, hl, rfl⟩)).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (congrArg Subtype.val (hcomm ⟨l, hD.LN hl⟩ hl)).symm
  · intro hs
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨l, hl, rfl⟩ := mem_img.mp hq
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hs) _ hl)

theorem Datum.card_aug_le (hD : Datum p N f L Bs Z) {x : G} (hx : x ∈ Bs) :
    Nat.card ↥(Subgroup.zpowers (f ⟨x, hD.BsN hx⟩) ⊔ (img N f Bs ⊓ img N f L)) ≤
      Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) := by
  let A : Subgroup G := Subgroup.zpowers x ⊔ (Bs ⊓ L)
  have hABs : A ≤ Bs := sup_le (Subgroup.zpowers_le.mpr hx) inf_le_left
  have hA : Subgroup.zpowers (f ⟨x, hD.BsN hx⟩) ⊔ (img N f Bs ⊓ img N f L) ≤ img N f A := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_img.mpr ⟨⟨x, hD.BsN hx⟩,
        (le_sup_left : Subgroup.zpowers x ≤ A) (Subgroup.mem_zpowers x), rfl⟩
    · intro q hq
      obtain ⟨s, hs, rfl⟩ := mem_img.mp hq.1
      have hsL : (s : G) ∈ L := (hD.mem_img_L_iff s).mp hq.2
      exact mem_img.mpr ⟨s, (le_sup_right : Bs ⊓ L ≤ A) ⟨hs, hsL⟩, rfl⟩
  calc Nat.card ↥(Subgroup.zpowers (f ⟨x, hD.BsN hx⟩) ⊔ (img N f Bs ⊓ img N f L))
      ≤ Nat.card ↥(img N f A) := Subgroup.card_le_of_le hA
    _ = Nat.card ↥A := hD.card_img hABs

end CFSG.StandardType.NsQuot

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.PhanDn.QTwo
open scoped commutatorElement

theorem qtwoDB3_shape_coords_of_induces {Q : Type} [Group Q] [Finite Q]
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {ψ : Su K 2 1 m →* Q}
    (hK : Nat.card K = 4) (hm : 3 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 m)) {s : Q} {v : DVec m} {ω : Kˣ}
    (hω : orderOf ω = 3)
    (hind : qTwoChartTwoThree_induces ψ s (fun i => ω ^ (v i).val)) (a b : Fin m) :
    (∀ c : Fin m → Kˣ, qTwoChartTwoThree_induces ψ s c → c a = c b) ↔ v a = v b := by
  constructor
  · intro h
    have heq := h _ hind
    have hmod := (pow_inj_mod (x := ω)).mp heq
    rw [hω, Nat.mod_eq_of_lt (ZMod.val_lt (v a)),
      Nat.mod_eq_of_lt (ZMod.val_lt (v b))] at hmod
    exact ZMod.val_injective 3 hmod
  · intro hv c hc
    obtain ⟨z, hz⟩ := qtwoDB3_ind_scalar hK hm hker hind hc
    rw [hz a, hz b]
    exact congrArg (fun x : ZMod 3 => z * ω ^ x.val) hv

section Original


theorem ggQTwoDUnit_B_shape_quot {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {Q : Type} [Group Q] [Finite Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {Z : Subgroup G}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 5 ≤ m)
    {ψ : Su K 2 1 m →* Q}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer (NsQuot.img _ f L) (NsQuot.img _ f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hbase : QTwoUnitBase 3 (NsQuot.img _ f B) (NsQuot.img _ f Bs) (f ⟨x, hx⟩)
      (NsQuot.img _ f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec m} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨(s : G), hs⟩)
        (fun i => ω ^ (βL (Additive.ofMul s) i).val)) :
    B = Bs ∨ ∃ a b : Fin m, a ≠ b ∧ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) a = βL (Additive.ofMul s) b) := by
  classical
  by_cases hBeq : B = Bs
  · exact Or.inl hBeq
  right
  obtain ⟨hBs, hxB, -, -, hBmax, hT⟩ := qtwoDB3_unpack hcfg
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hBsCard : Nat.card ↥Bs = 3 ^ m := by
    rw [← hD.card_img le_rfl]
    exact hbase.card_bs
  have hAug : 3 ^ (m - 1) ≤ Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) :=
    (qtwoDB3_card_aug hbase hm).trans (hD.card_aug_le hxBs)
  have hS : LargeEvenSStar 3 B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hS.2.2.2.1.2.2.1
  have hLn : ∀ t ∈ Subgroup.centralizer ({x} : Set G),
      t ∈ Subgroup.normalizer (L : Set G) := by
    intro t ht
    exact mem_normalizer_of_sstar hS
      (ggLNoncyclicInput_holds G 3 B x L hcfg.1.1.1) ht
  obtain ⟨T, hTx, hT2, hBT, t, ht, b, hb, hnt⟩ :=
    qtwoDB3_exists_t_of_aug hBs hxB hBmax hT hBsCard hAug (Or.inl hBeq)
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let Bq : Subgroup Q := NsQuot.img N f B
  let Sq : Subgroup Q := NsQuot.img N f Bs
  let Lq : Subgroup Q := NsQuot.img N f L
  let Tq : Subgroup Q := NsQuot.img N f T
  have hTN : T ≤ N := fun u hu => hLn u (hTx hu)
  have hBN : B ≤ N := hBs.1.trans hD.BsN
  have hmapNorm : ∀ A C : Subgroup G, A ≤ Subgroup.normalizer (C : Set G) →
      NsQuot.img N f A ≤ Subgroup.normalizer (NsQuot.img N f C : Set Q) := by
    intro A C hAC
    have h' : A.subgroupOf N ≤ Subgroup.normalizer (C.subgroupOf N : Set ↥N) :=
      (Subgroup.comap_mono hAC).trans (Subgroup.le_normalizer_comap N.subtype)
    exact (Subgroup.map_mono h').trans (Subgroup.le_normalizer_map f)
  have hT2N : IsPGroup 2 ↥(T.subgroupOf N) := by
    intro u
    obtain ⟨k, hk⟩ := hT2 (⟨((u : ↥N) : G), u.2⟩ : ↥T)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun w : ↥T => (w : G)) hk
  have hT2q : IsPGroup 2 ↥Tq := hT2N.map f
  have hBnorm : Bq ≤ Subgroup.normalizer (ψ.range : Set Q) := by
    rw [hbase.range]
    exact hmapNorm B L hBN
  have hTnorm : Tq ≤ Subgroup.normalizer (ψ.range : Set Q) := by
    rw [hbase.range]
    exact hmapNorm T L hTN
  have hBTq : Bq ≤ Subgroup.normalizer (Tq : Set Q) := hmapNorm B T hBT
  have hBdiag : ∀ s ∈ Bq, ∃ c : Fin m → Kˣ, qTwoChartTwoThree_induces ψ s c := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := NsQuot.mem_img.mp hs
    exact ⟨_, hind ⟨(u : G), hBs.1 hu⟩ u.2⟩
  have hntq : ∃ t ∈ Tq, ∃ b ∈ Bq, ⁅t, b⁆ ∉ Subgroup.centralizer (ψ.range : Set Q) := by
    let tn : ↥N := ⟨t, hTN ht⟩
    let bn : ↥N := ⟨b, hBN hb⟩
    refine ⟨f tn, NsQuot.mem_img.mpr ⟨tn, ht, rfl⟩,
      f bn, NsQuot.mem_img.mpr ⟨bn, hb, rfl⟩, ?_⟩
    intro hc
    rw [hbase.range, ← map_commutatorElement] at hc
    have h := (hD.mem_centralizer_img_iff hLperf ⁅tn, bn⁆).mp hc
    exact hnt h
  obtain ⟨a, a', haa', hall⟩ := qtwoDB3_core hbase.card_field hm hbase.hyp.ker
    hT2q hBnorm hTnorm hBTq hBdiag hntq
  obtain ⟨Hq, hHqS, -, hcardHq, hHqiff⟩ := qtwoDB3_exists_Hab hbase hm haa'
  let Hs : Subgroup ↥Bs := (Hq.subgroupOf Sq).comap hD.tau.toMonoidHom
  let H : Subgroup G := Hs.map Bs.subtype
  have hHiff : ∀ s : ↥Bs, (s : G) ∈ H ↔ (hD.tau s : Q) ∈ Hq := by
    intro s
    change Bs.subtype s ∈ Hs.map Bs.subtype ↔ (hD.tau s : Q) ∈ Hq
    rw [Subgroup.mem_map_iff_mem (Subgroup.subtype_injective Bs)]
    change hD.tau s ∈ Hq.subgroupOf Sq ↔ (hD.tau s : Q) ∈ Hq
    rw [Subgroup.mem_subgroupOf]
  have hBH : B ≤ H := by
    intro s hs
    apply (hHiff ⟨s, hBs.1 hs⟩).mpr
    have hqB : (hD.tau ⟨s, hBs.1 hs⟩ : Q) ∈ Bq :=
      NsQuot.mem_img.mpr ⟨⟨s, hBN hs⟩, hs, rfl⟩
    apply (hHqiff (hD.tau ⟨s, hBs.1 hs⟩)).mpr
    exact hall _ hqB
  have hHsmap : Hs.map hD.tau.toMonoidHom = Hq.subgroupOf Sq :=
    Subgroup.map_comap_eq_self_of_surjective hD.tau.surjective _
  have hHcard : Nat.card ↥H = Nat.card ↥Hq := by
    calc Nat.card ↥H = Nat.card ↥Hs :=
          Subgroup.card_map_of_injective (Subgroup.subtype_injective Bs)
      _ = Nat.card ↥(Hs.map hD.tau.toMonoidHom) :=
          (Subgroup.card_map_of_injective (f := hD.tau.toMonoidHom) hD.tau.injective).symm
      _ = Nat.card ↥(Hq.subgroupOf Sq) :=
          congrArg (fun S : Subgroup ↥Sq => Nat.card ↥S) hHsmap
      _ = Nat.card ↥Hq := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHqS).toEquiv
  have hcardH : Nat.card ↥Bs = 3 * Nat.card ↥H := by
    rw [← hD.card_img le_rfl, hHcard]
    exact hcardHq
  have hcard : Nat.card ↥H ≤ Nat.card ↥B := by
    have h := hBs.2.2.1
    omega
  have hBeqH : B = H := Subgroup.eq_of_le_of_card_ge hBH hcard
  refine ⟨a, a', haa', fun s => ?_⟩
  rw [hBeqH, hHiff, hHqiff (hD.tau s)]
  rw [NsQuot.Datum.tau_apply]
  exact qtwoDB3_shape_coords_of_induces hbase.card_field (by omega) hbase.hyp.ker hω
    (hind s (hD.BsN s.2)) a a'


theorem ggQTwoDUnitSix_B_shape (_hTBF : GGTBFixInput) (_hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) (e' : Fin 6 ≃ ι)
    (_hM : M = (ggCoxeterMatrixD 6).reindex e')
    (_hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L)
    {Q : Type} [Group Q] [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    {K : Type} [Field K] [Finite K] [CharP K 2] {ψ : Su K 2 1 6 →* Q}
    {ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (NsQuot.img _ f L) (NsQuot.img _ f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hbase : QTwoUnitBase 3 (NsQuot.img _ f B) (NsQuot.img _ f Bs) (f ⟨x, hx⟩)
      (NsQuot.img _ f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨(s : G), hs⟩)
        (fun i => ω ^ (βL (Additive.ofMul s) i).val)) :
    B = Bs ∨ ∃ u v : Fin 6, u ≠ v ∧ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) u = βL (Additive.ofMul s) v) :=
  ggQTwoDUnit_B_shape_quot hcfg.1 hD (by decide) hbase hω hind

end Original

private theorem unitSix_exists_pair_off (u v : Fin 6) :
    ∃ a c : Fin 6, a ≠ c ∧ a ≠ u ∧ a ≠ v ∧ c ≠ u ∧ c ≠ v := by
  revert u v
  decide +kernel

theorem ggQTwoDUnitSix_selected_coordinates {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {βL : Additive ↥Bs ≃+ DVec 6} {u v : Fin 6} (hBBs : B ≤ Bs)
    (hshape : B = Bs ∨ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) u = βL (Additive.ofMul s) v)) :
    ∃ a c : Fin 6, a ≠ c ∧ a ≠ u ∧ a ≠ v ∧ c ≠ u ∧ c ≠ v ∧
      ∃ b' : ↥Bs, βL (Additive.ofMul b') = Pi.single c 1 ∧ (b' : G) ∈ B := by
  obtain ⟨a, c, hac, hau, hav, hcu, hcv⟩ := unitSix_exists_pair_off u v
  let b' : ↥Bs := Additive.toMul (βL.symm (Pi.single c 1))
  have hb' : βL (Additive.ofMul b') = Pi.single c 1 := βL.apply_symm_apply _
  exact ⟨a, c, hac, hau, hav, hcu, hcv, b', hb',
    ggQTwoDUnit_mem_B hcu hcv hBBs hshape hb'⟩

end CFSG.StandardType.QTwo
