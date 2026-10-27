module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem412
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofPair
import CFSG.RankThree.PartTwo.Sec21.Item2130Res5ProofLThree
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofTypesCent
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck158

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof158Cartan (actBar actBar_eq_one_iff actBar_eq_one_of_commute)

open CFSG.Assembly.RankThreeEven (projImage)

open Matrix (ProjGenLinGroup)


variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev innAut (L : Subgroup G) :
    Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
  (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
    MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range

private noncomputable def innDiag {L : Subgroup G} {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K)) :
    Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) where
  carrier := {σ | ∃ y ∈ glPi π 3 (p ^ f) K, ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
    ((e (σ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹}
  mul_mem' := by
    rintro σ₁ σ₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
    refine ⟨y₁ * y₂, Subgroup.mul_mem _ hy₁ hy₂, fun z => ?_⟩
    rw [MulAut.mul_apply, h₁, h₂, map_mul]
    group
  one_mem' := ⟨1, Subgroup.one_mem _, fun z => by simp⟩
  inv_mem' := by
    rintro σ ⟨y, hy, h⟩
    refine ⟨y⁻¹, Subgroup.inv_mem _ hy, fun z => ?_⟩
    have h1 := h (σ⁻¹ z)
    rw [MulAut.apply_inv_self] at h1
    rw [map_inv]
    calc (e (σ⁻¹ z) : ProjGenLinGroup (Fin 3) K)
        = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y *
            (e (σ⁻¹ z) : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) *
          ProjGenLinGroup.mk y := by group
      _ = _ := by rw [← h1]; group

private theorem innAut_le_innDiag {L : Subgroup G} {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K)
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K)) :
    innAut L ≤ innDiag e := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨s, hs, hse⟩ := (e w).2
  refine ⟨s, slPi_le_glPi (fun h => by subst h; exact hK.unitary) hs, fun z => ?_⟩
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, ← hse]

private noncomputable def actIn (L : Subgroup G)
    (H : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) : Subgroup G :=
  (H.comap (actBar L)).map (Subgroup.normalizer (L : Set G)).subtype

private theorem mem_actIn_iff {L : Subgroup G}
    {H : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))} {g : G} :
    g ∈ actIn L H ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G), actBar L ⟨g, hg⟩ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

private theorem actIn_mono {L : Subgroup G}
    {H H' : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))} (h : H ≤ H') :
    actIn L H ≤ actIn L H' := fun g hg => by
  obtain ⟨hgN, hg'⟩ := mem_actIn_iff.mp hg
  exact mem_actIn_iff.mpr ⟨hgN, h hg'⟩

private theorem sup_le_actIn_innAut {L : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hLc : ∀ l ∈ L, l * c = c * l) :
    Subgroup.zpowers c ⊔ L ≤ actIn L (innAut L) := by
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun l hl => ?_)
  · exact mem_actIn_iff.mpr ⟨hcN, by rw [actBar_eq_one_of_commute hcN hLc]; exact one_mem _⟩
  · refine mem_actIn_iff.mpr ⟨Subgroup.le_normalizer hl, QuotientGroup.mk' _ ⟨l, hl⟩, ?_⟩
    ext z
    induction z using QuotientGroup.induction_on with
    | H m => rfl

open CFSG.Assembly.LowTwoRank (StatedScalars) 
in
private theorem not_mem_actIn_innAut_of_type_three {L : Subgroup G}
    (hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L)) {a : G}
    (ha : InducesTypeOn L a 3) : a ∉ actIn L (innAut L) := by
  intro hmem
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := ha
  obtain ⟨_hg, w, hw⟩ := mem_actIn_iff.mp hmem
  have hPerf : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply Sec4.not_inner_of_type3 hK hq hyH hy3
  obtain ⟨s, hs, hse⟩ := (e w).2
  refine ⟨s, hs, ?_⟩
  have hmod : ∀ m ∈ slPi π 3 (p ^ f) K,
      s⁻¹ * y * m * (s⁻¹ * y)⁻¹ * m⁻¹ ∈ StatedScalars (Fin 3) K := by
    intro m hm
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
    set z := e.symm ⟨ProjGenLinGroup.mk m, Subgroup.mem_map_of_mem _ hm⟩ with hz
    have hez : (e z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk m := by
      rw [hz, MulEquiv.apply_symm_apply]
    have h1 := hact z
    have h2 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, hxN⟩) z = w * z * w⁻¹ := by
      change actBar L ⟨a, hxN⟩ z = _
      rw [← hw, MulAut.conj_apply]
    rw [h2, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ← hse, hez] at h1
    simp only [map_mul, map_inv]
    calc (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          ((ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk m)⁻¹ =
        (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk m)⁻¹ := by group
      _ = 1 := by rw [← h1]; group
  intro m hm
  have hc := Sec4.commute_of_comm_mod_scalars hmod m hm
  calc y * m * y⁻¹ = s * (s⁻¹ * y * m) * y⁻¹ := by group
    _ = s * (m * (s⁻¹ * y)) * y⁻¹ := by rw [hc]
    _ = s * m * s⁻¹ := by group

section Certs


private theorem alt412_three (h41 : Sec4.Item4_1LargePrime) {A L A' : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hA'e : CFSG.Assembly.IsElemAbelian 3 A') (hA'27 : Nat.card A' = 27)
    (hA'max : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A' ≤ B → B = A')
    (hcA' : c ∈ A') (hc1 : c ≠ 1) (hA'C : A' ≤ Subgroup.centralizer ({c} : Set G))
    (hA'N : A' ≤ Subgroup.normalizer (L : Set G))
    (hCA' : A' ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c) :
    A' ≤ L ⊔ Subgroup.zpowers c ∨ Sec4.IsTypeCOn A' L ∨ ∃ a ∈ A', Sec4.InducesTypeOn L a 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA'p : IsPGroup 3 A' := fun g => ⟨1, Subtype.ext (by simpa using hA'e.2 g g.2)⟩
  have hG4 := hR.toTheoremFourHyp
  have hLA' : L ⊔ A' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one hG4 hc1
      (eq_top_iff.mpr (htop ▸ sup_le hR.le_centralizer hA'C))
  have hΛ : SectionFourHyp ↥(L ⊔ A') := hG4.sectionFourHyp hLA'
  obtain ⟨Φ₀, hΦ₀⟩ := Sec21.Item211Proof.exists_lEquiv hA'N
  have hq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hR.mem_thetaComponentsAt
  have hX := Sec21.Item211Proof.sectionFourHyp_quotX h41 hΛ hA'p hA'N Φ₀ hq
  have hq₁ : IsQuasisimple (Sec21.Item211Proof.lOne L A') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Φ₀ hq
  have hmax := Sec21.Item211Proof.maximal_aOne (L := L) hA'e hA'max
  have hcard₁ : Nat.card (Sec21.Item211Proof.aOne L A') = 27 := by
    rw [← Nat.card_congr (Sec21.Item211Proof.aEquiv (L := L) hA'p).toEquiv, hA'27]
  have hc₁ : orderOf (Sec21.Item211Proof.piX L A' ⟨c, Subgroup.mem_sup_right hcA'⟩) = 3 := by
    have h1 : (Sec21.Item211Proof.piX L A' ⟨c, Subgroup.mem_sup_right hcA'⟩) =
        ((Sec21.Item211Proof.aEquiv (L := L) hA'p ⟨c, hcA'⟩ : Sec21.Item211Proof.aOne L A') :
          Sec21.Item211Proof.QuotX L A') := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA'e.2 c hcA') hc1
  have hCA₁ := Sec21.Item211Proof.aOne_inf_centralizer hA'p hA'N hcA' hCA'
  have hL₁ : ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
      Sec4.IsoLThreePi ↥(Sec21.Item211Proof.lOne L A') p e :=
    ⟨p, e, inferInstance, he, Sec8.Item82OneProof.isoLThreePi_of_mulEquiv Φ₀.symm hiso⟩
  rcases Sec4.rank3II_4_12 (Sec21.Item211Proof.QuotX L A') hX (Sec21.Item211Proof.lOne L A')
      (Sec21.Item211Proof.normal_lOne hA'N) hL₁ hq₁ (Sec21.Item211Proof.aOne L A') hmax
      (by omega) _ hc₁ hCA₁ with ⟨-, hsup, -⟩ | ⟨-, hTC'⟩ | ⟨-, ⟨a₁, ha₁, ha₁3⟩, -⟩ | ⟨h81, -⟩
  · exact Or.inl (Sec21.Item2130Res5Proof.le_sup_zpowers_of_sup_eq hA'p hA'N hcA' hsup)
  · exact Or.inr (Or.inl (Sec21.Item211Proof.isTypeCOn_of_lOne hA'N hΦ₀ hTC'))
  · obtain ⟨a, haA', rfl⟩ := Sec21.Item211Proof.exists_eq_piX_of_mem_aOne ha₁
    exact Or.inr (Or.inr ⟨a, haA',
      Sec21.Item2130Res5Proof.inducesTypeOn_of_lOne hA'N hΦ₀ haA' ha₁3⟩)
  · omega



theorem exists_model_inndiag (h41 : Sec4.Item4_1LargePrime) {A L F P' : Subgroup G} {c : G}
    (hR : Sec15R G A c L) (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) {x : G}
    (hP'def : P' = F ⊔ Subgroup.zpowers x)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hFeq : F = Subgroup.zpowers c ⊔ (F ⊓ L)) (hF9 : Nat.card (F ⊓ L : Subgroup G) = 9)
    (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (F : Set G)) (hxF : x ∉ F)
    (hP'N : P' ≤ Subgroup.normalizer (L : Set G))
    (hP'c : P' ≤ Subgroup.centralizer ({c} : Set G))
    (hmax : ∀ E : Subgroup G, E ≤ P' → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : PiField π p f K)
      (_ : ModThree π (p ^ f)) (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        projImage (slPi π 3 (p ^ f) K)), 2 < p ^ f ∧
      ∀ (g : G) (hg : g ∈ P'), ∃ y ∈ glPi π 3 (p ^ f) K,
        ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
          ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hP'N hg⟩) z) :
            ProjGenLinGroup (Fin 3) K)) =
            ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) *
              (ProjGenLinGroup.mk y)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p₀, e₀, hp₀, he₀, hiso⟩ := hL3
  obtain ⟨π₀, K₀, _, hK₀, hq₀, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he₀ hiso
  have hquasi : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hR.mem_thetaComponentsAt
  have hq2 : 2 < p₀ ^ e₀ := Sec14.L3PGL.two_lt_of_model hquasi hK₀ hq₀ ψ
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv ψ (Sec13.center_projImage_slPi hK₀ hq₀ hq2)
  have hc3 : c ^ 3 = 1 := by
    have h3 := hR.orderOf_eq
    rw [← h3]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := hR.ne_one
  have hcL : c ∉ L := Sec12.Proof128.not_mem_of_center_eq_bot hR.mem_thetaComponentsAt hZ hc3 hc1
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hR.le_centralizer hl)
  subst hP'def
  have hxP' : x ∈ F ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hFP' : F ≤ F ⊔ Subgroup.zpowers x := le_sup_left
  have hcF : c ∈ F := by
    rw [hFeq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hP'N hxP'
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hP'N (hFP' hcF)
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFp : IsPGroup 3 F := Sec5.isPGroup_of_isElemAbelian hF
  have hx1 : x ≠ 1 := fun h1 => hxF (h1 ▸ F.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxp : IsPGroup 3 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hP'3 : IsPGroup 3 (F ⊔ Subgroup.zpowers x : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hxp hFp (Subgroup.zpowers_le.mpr hxN)
  have hBp : IsPGroup 3 (F ⊓ L : Subgroup G) := hFp.to_le inf_le_left
  have hB1 : (F ⊓ L : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hF9
    omega
  have hxB : Subgroup.zpowers x ≤ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hxN y
    have h2 := Subgroup.mem_normalizer_iff.mp hxL y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  obtain ⟨d, hdB, hdx, hd3, hd1⟩ := Sec4.exists_mem_centralizer_pow_three hxp hBp hxB hB1
  have hdF : d ∈ F := hdB.1
  have hdL : d ∈ L := hdB.2
  have hdx' : x * d = d * x := Subgroup.mem_centralizer_iff.mp hdx x (Subgroup.mem_zpowers x)
  have hcd : c * d = d * c := hFc c hcF d hdF
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (hP'c hxP')
  have hcT : c ∈ thetaQuotCentralizer L :=
    (actBar_eq_one_iff ⟨c, hcN⟩).mp (actBar_eq_one_of_commute hcN hLc)
  have hker : ∀ a ∈ F ⊔ Subgroup.zpowers x, a ^ 3 = 1 → a ∈ thetaQuotCentralizer L →
      a ∈ Subgroup.zpowers c := by
    intro a ha ha3 haC
    obtain ⟨-, haθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp haC
    have haB : ∀ b ∈ F ⊓ L, a * b = b * a := by
      intro b hb
      have h1 := haθ b hb.2
      have hbP' : b ∈ F ⊔ Subgroup.zpowers x := Subgroup.mem_sup_left hb.1
      have h2 : b⁻¹ * (a * b * a⁻¹) ∈ F ⊔ Subgroup.zpowers x :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hbP')
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hbP') (Subgroup.inv_mem _ ha))
      have h3 := Proof158Cartan.eq_one_of_mem_theta_of_isPGroup hP'3 h2 h1
      calc a * b = b * (b⁻¹ * (a * b * a⁻¹)) * a := by group
        _ = b * a := by rw [h3, mul_one]
    have hac : a * c = c * a := Subgroup.mem_centralizer_singleton_iff.mp (hP'c ha)
    have haF : ∀ f ∈ F, f * a = a * f := by
      intro f hf
      have hFa : F ≤ Subgroup.centralizer ({a} : Set G) :=
        hFeq.le.trans (sup_le
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac.symm))
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (haB b hb).symm))
      exact Subgroup.mem_centralizer_singleton_iff.mp (hFa hf)
    have haFmem : a ∈ F := by
      have hFa := Sec15.isElemAbelian_sup_zpowers hF ha3 haF
      have heq := hmax F hFP' hF hF27 (F ⊔ Subgroup.zpowers a) hFa le_sup_left
      rw [← heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    have hamem : a ∈ (F ⊓ L) ⊔ Subgroup.zpowers c := by
      rw [sup_comm, ← hFeq]
      exact haFmem
    obtain ⟨b, hb, m, -, rfl⟩ := Sec13.exists_mul_pow_of_mem_sup hc3
      (fun t ht => by rw [hFc c hcF t ht.1, mul_inv_cancel_right]; exact ht) hamem
    have hbC : b ∈ thetaQuotCentralizer L := by
      have h1 := Subgroup.mul_mem _ haC (Subgroup.inv_mem _ (Subgroup.pow_mem _ hcT m))
      rwa [mul_inv_cancel_right] at h1
    have hbθ := Sec4.Item424Proof.mem_theta_of_mem_thetaQuotCentralizer hZ hb.2 hbC
    have hb1 : b = 1 :=
      Proof158Cartan.eq_one_of_mem_theta_of_isPGroup hP'3 (Subgroup.mem_sup_left hb.1) hbθ
    rw [hb1, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) m
  have hD : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers d ⊔ Subgroup.zpowers c) :=
    Sec13.isElemAbelian_zpowers_sup hd3 hc3 hcd.symm
  have hcnd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hD9 : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    Sec4.card_zpowers_sup_zpowers hc3 (orderOf_eq_prime hd3 hd1) hcnd hcd
  have hDF : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ F :=
    sup_le (Subgroup.zpowers_le.mpr hdF) (Subgroup.zpowers_le.mpr hcF)
  have hxD : x ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := fun h => hxF (hDF h)
  have hDx : ∀ a ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c, a * x = x * a := by
    have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdx'.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm))
    exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  obtain ⟨hE₁, hE₁card⟩ := Sec5.isElemAbelian_sup_zpowers hD hxD hx3 hDx
  have hE₁27 : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers x :
      Subgroup G) = 27 := by rw [hE₁card, hD9]
  have hE₁P' : Subgroup.zpowers d ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers x ≤
      F ⊔ Subgroup.zpowers x := sup_le (hDF.trans le_sup_left) le_sup_right
  set E₁ := Subgroup.zpowers d ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers x
  have hDE₁ : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ E₁ := le_sup_left
  have hxE₁ : x ∈ E₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hcE₁ : c ∈ E₁ := hDE₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hE₁C : E₁ ≤ Subgroup.centralizer ({c} : Set G) := hE₁P'.trans hP'c
  have hE₁N : E₁ ≤ Subgroup.normalizer (L : Set G) := hE₁P'.trans hP'N
  have hCE₁ : E₁ ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := by
    refine le_antisymm (fun a ha => hker a (hE₁P' ha.1) (hE₁.2 a ha.1) ha.2) fun a ha => ⟨?_, ?_⟩
    · exact Subgroup.zpowers_le.mpr hcE₁ ha
    · exact Subgroup.zpowers_le.mpr hcT ha
  have hmaxE₁ := hmax E₁ hE₁P' hE₁ hE₁27
  have hbase := sup_le_actIn_innAut hcN hLc
  have hFle : F ≤ Subgroup.zpowers c ⊔ L := hFeq.le.trans (sup_le_sup_left inf_le_right _)
  suffices key : ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : PiField π p f K)
      (_ : ModThree π (p ^ f)) (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        projImage (slPi π 3 (p ^ f) K)), F ⊔ Subgroup.zpowers x ≤ actIn L (innDiag e) by
    obtain ⟨π, p, f, K, _, hK, hq, e, hle⟩ := key
    refine ⟨π, p, f, K, inferInstance, hK, hq, e,
      Sec14.L3PGL.two_lt_of_model hquasi hK hq e, fun g hg => ?_⟩
    obtain ⟨hgN, y, hy, h⟩ := mem_actIn_iff.mp (hle hg)
    exact ⟨y, hy, h⟩
  rcases alt412_three h41 hR he₀ hiso hE₁ hE₁27 hmaxE₁ hcE₁ hc1 hE₁C hE₁N hCE₁ with
    h1 | h2 | ⟨a, haE₁, ha3⟩
  ·
    refine ⟨π₀, p₀, e₀, K₀, inferInstance, hK₀, hq₀, ψ, ?_⟩
    have hb := hbase.trans (actIn_mono (innAut_le_innDiag hK₀ ψ))
    have hxcL : x ∈ Subgroup.zpowers c ⊔ L := by
      rw [sup_comm]
      exact h1 hxE₁
    exact sup_le (hFle.trans hb) (Subgroup.zpowers_le.mpr (hb hxcL))
  ·
    obtain ⟨π', p', f', K', _, hK', hq', e', D, hDC, hD1, -⟩ := h2
    refine ⟨π', p', f', K', inferInstance, hK', hq', e', ?_⟩
    have hb := hbase.trans (actIn_mono (innAut_le_innDiag hK' e'))
    refine sup_le (hFle.trans hb) (Subgroup.zpowers_le.mpr ?_)
    refine mem_actIn_iff.mpr ⟨hxL, ?_⟩
    obtain ⟨y, hyD, hy⟩ := hD1 _ (mem_autThetaQuot_iff.mpr ⟨x, hxL, hxE₁, rfl⟩)
    exact ⟨y, hDC.1 hyD, hy⟩
  ·
    have hout := not_mem_actIn_innAut_of_type_three hquasi.1 ha3
    obtain ⟨haN, π', p', f', K', _, hK', hq', e', y, hyH, hy3, hact⟩ := ha3
    refine ⟨π', p', f', K', inferInstance, hK', hq', e', ?_⟩
    have hb := hbase.trans (actIn_mono (innAut_le_innDiag hK' e'))
    have haI : a ∈ actIn L (innDiag e') := mem_actIn_iff.mpr ⟨haN, y, hyH, hact⟩
    have hDcL : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ Subgroup.zpowers c ⊔ L :=
      sup_le (le_trans (Subgroup.zpowers_le.mpr hdL) le_sup_right) le_sup_left
    have haD : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := fun h => hout (hbase (hDcL h))
    have ha3' : a ^ 3 = 1 := hE₁.2 a haE₁
    have hDa : ∀ b ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c, b * a = a * b := fun b hb' =>
      congrArg Subtype.val (hE₁.1.is_comm.comm ⟨b, hDE₁ hb'⟩ ⟨a, haE₁⟩)
    obtain ⟨-, hDa27⟩ := Sec5.isElemAbelian_sup_zpowers hD haD ha3' hDa
    have hDaE : Subgroup.zpowers d ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers a = E₁ :=
      Subgroup.eq_of_le_of_card_ge (sup_le hDE₁ (Subgroup.zpowers_le.mpr haE₁))
        (by omega)
    have hxDa : x ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers a := hDaE ▸ hxE₁
    refine sup_le (hFle.trans hb) (Subgroup.zpowers_le.mpr ?_)
    exact (sup_le (hDcL.trans hb) (Subgroup.zpowers_le.mpr haI)) hxDa


end Certs

end CFSG.RankThree.PartTwo.Sec15.Liebeck158
