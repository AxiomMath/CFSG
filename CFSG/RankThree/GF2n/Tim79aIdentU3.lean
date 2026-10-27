module

public import CFSG.RankThree.GF2n.Tim79aIdentNormalizer
public import CFSG.RankThree.GF2n.Tim79aIdentL2Sz
public import CFSG.RankThree.GF2n.Tim79aSec23Reductions
import CFSG.StronglyEmbedded.BenderU3Commutator
import CFSG.StronglyEmbedded.BenderU3Generation
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.StronglyEmbedded.BenderCentre
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_mul_central {K : Type*} [Group K] {z₁ z₂ s t : K}
    (h1s : Commute z₁ s) (h1t : Commute z₁ t) (h12 : Commute z₁ z₂)
    (h2s : Commute z₂ s) (h2t : Commute z₂ t) : ⁅z₁ * s, z₂ * t⁆ = ⁅s, t⁆ := by
  have hX : Commute z₁ (z₂ * t) := h12.mul_right h1t
  have hs : Commute z₁ (s * (z₂ * t) * s⁻¹) := (h1s.mul_right hX).mul_right h1s.inv_right
  have step1 : (z₁ * s) * (z₂ * t) * (z₁ * s)⁻¹ = s * (z₂ * t) * s⁻¹ := by
    calc (z₁ * s) * (z₂ * t) * (z₁ * s)⁻¹ = z₁ * (s * (z₂ * t) * s⁻¹) * z₁⁻¹ := by group
      _ = s * (z₂ * t) * s⁻¹ := by rw [hs.eq]; group
  have h2 : Commute z₂ (s * t * s⁻¹ * t⁻¹) :=
    ((h2s.mul_right h2t).mul_right h2s.inv_right).mul_right h2t.inv_right
  have step2 : s * (z₂ * t) = z₂ * (s * t) := by
    rw [← mul_assoc, ← h2s.eq, mul_assoc]
  simp only [commutatorElement_def]
  rw [step1]
  calc s * (z₂ * t) * s⁻¹ * (z₂ * t)⁻¹ = z₂ * (s * t * s⁻¹ * t⁻¹) * z₂⁻¹ := by
        rw [step2]; group
    _ = s * t * s⁻¹ * t⁻¹ := by rw [h2.eq]; group

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem isPGroup_barOf_P (hc : MinCex M V Q P H) : IsPGroup 2 (barOf V H P) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := mem_barOf_iff.mp y.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hc.isPGroup_P ⟨(p : G), hp⟩
  refine ⟨k, ?_⟩
  have h0 : (⟨(p : G), hp⟩ : P) ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have h1 : (p : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val h0
  have h2 : p ^ 2 ^ k = 1 := Subtype.ext (by simpa using h1)
  apply Subtype.ext
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hpy, ← map_pow, h2, map_one]

theorem centralizes_of_tildeAut_eq_one (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    {c : Hbar V H} (hcx : ∀ x : Xbar V H,
      projZ V H (haveI := normal_barOf_xOf V H; MulAut.conjNormal c x) = projZ V H x) :
    ∀ x : Xbar V H, c * (x : Hbar V H) * c⁻¹ = (x : Hbar V H) := by
  haveI := normal_barOf_xOf V H
  have hD : ∀ d ∈ Dy V H, (MulAut.conjNormal c d : Xbar V H) = d := by
    intro d hdD
    set d' : Xbar V H := MulAut.conjNormal c d with hd'
    have hd'D : d' ∈ Dy V H := by
      show (d' : Hbar V H) ∈ dbarOf V H
      rw [hd', MulAut.conjNormal_apply]
      exact hc.conj_mem_dbarOf hdD
    have hz : d⁻¹ * d' ∈ Subgroup.center (Xbar V H) := by
      have h1 : projZ V H (d⁻¹ * d') = 1 := by
        rw [map_mul, map_inv, hd', hcx d]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hz1 : d⁻¹ * d' = 1 :=
      noCentralTwist hd _ hz d hdD (by rwa [mul_inv_cancel_left])
    exact (inv_mul_eq_one.mp hz1).symm
  have hall : ∀ x : Xbar V H, (MulAut.conjNormal c x : Xbar V H) = x := by
    intro x
    have hle : Subgroup.closure (Dy V H) ≤
        MonoidHom.eqLocus (MulAut.conjNormal c : MulAut (Xbar V H)).toMonoidHom
          (MonoidHom.id (Xbar V H)) :=
      (Subgroup.closure_le _).mpr fun d hdD => hD d hdD
    have hx : x ∈ Subgroup.closure (Dy V H) := by rw [hd.gen]; exact Subgroup.mem_top x
    exact hle hx
  intro x
  have := congrArg (fun y : Xbar V H => (y : Hbar V H)) (hall x)
  simpa [MulAut.conjNormal_apply] using this


theorem normalizer_le_of_Rtilde_le (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hBG : IsBenderGroup (XbarZ V H)) (S : Sylow 2 (XbarZ V H))
    (hVS : VZ V H ≤ sylowCenter (S : Subgroup (XbarZ V H)))
    (hRZ : Rtilde V H P ≤ sylowCenter (S : Subgroup (XbarZ V H)))
    (hZc : sylowCenter (S : Subgroup (XbarZ V H)) ≤
      ⁅(S : Subgroup (XbarZ V H)), (S : Subgroup (XbarZ V H))⁆)
    (hAut : ∀ φ : MulAut (XbarZ V H),
      (∀ s ∈ (S : Subgroup (XbarZ V H)), φ s ∈ (S : Subgroup (XbarZ V H))) →
      (∀ z ∈ sylowCenter (S : Subgroup (XbarZ V H)), φ z = z) →
      (∀ s ∈ (S : Subgroup (XbarZ V H)),
        s⁻¹ * φ s ∈ sylowCenter (S : Subgroup (XbarZ V H))) →
      ∃ s ∈ (S : Subgroup (XbarZ V H)), φ = MulAut.conj s) :
    ∀ n ∈ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set (XbarZ V H)),
      n ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
  haveI := normal_barOf_xOf V H
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨Sb, hRSb, hSmap⟩ := hc.exists_sylow_over hd hBG hVS
  have hSN : ∀ s ∈ (S : Subgroup (XbarZ V H)),
      s ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := fun s hs =>
    mem_normalizer_VZ_of_le_sylowCenter hVS hs
  have hSbN : ∀ sb ∈ (Sb : Subgroup (Xbar V H)),
      sb ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H)) := by
    intro sb hsb
    refine hc.mem_normalizer_Vy_of_tilde hd (hSN _ ?_)
    rw [← hSmap]
    exact ⟨sb, hsb, rfl⟩
  have hpc : ∀ p ∈ barOf V H P, ∃ sb : Xbar V H, sb ∈ (Sb : Subgroup (Xbar V H)) ∧
      ∀ x : Xbar V H, ((sb : Hbar V H)⁻¹ * p) * (x : Hbar V H) * ((sb : Hbar V H)⁻¹ * p)⁻¹ =
        (x : Hbar V H) := by
    intro p hp
    set α : MulAut (XbarZ V H) := tildeAut V H p with hα
    have hαs : ∀ s ∈ (S : Subgroup (XbarZ V H)), ∃ z ∈ sylowCenter (S : Subgroup (XbarZ V H)),
        α s = z * s := by
      intro s hs
      rw [← hSmap] at hs
      obtain ⟨sb, hsb, rfl⟩ := hs
      obtain ⟨r', hr', hr'eq⟩ := hc.commutator_mem_Rbar (hSbN sb hsb) hp
      refine ⟨(projZ V H r')⁻¹, hRZ ⟨r', hr', rfl⟩ |> fun h =>
        Subgroup.inv_mem _ h |> fun h => ?_, ?_⟩
      · exact h
      · have hxe : (MulAut.conjNormal p sb : Xbar V H) = r'⁻¹ * sb := by
          apply Subtype.ext
          rw [MulAut.conjNormal_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hr'eq]
          group
        have := tildeAut_mk (V := V) (H := H) p sb
        rw [hα]
        change tildeAut V H p (projZ V H sb) = _
        rw [show projZ V H sb = QuotientGroup.mk' (Subgroup.center (Xbar V H)) sb from rfl,
          this, hxe, map_mul, map_inv]
        rfl
    have hZS : sylowCenter (S : Subgroup (XbarZ V H)) ≤ (S : Subgroup (XbarZ V H)) :=
      sylowCenter_le _
    have h1 : ∀ s ∈ (S : Subgroup (XbarZ V H)), α s ∈ (S : Subgroup (XbarZ V H)) := by
      intro s hs
      obtain ⟨z, hz, hzs⟩ := hαs s hs
      rw [hzs]
      exact (S : Subgroup (XbarZ V H)).mul_mem (hZS hz) hs
    have h3 : ∀ s ∈ (S : Subgroup (XbarZ V H)),
        s⁻¹ * α s ∈ sylowCenter (S : Subgroup (XbarZ V H)) := by
      intro s hs
      obtain ⟨z, hz, hzs⟩ := hαs s hs
      have hc' : z * s = s * z := ((mem_sylowCenter.mp hz).2 s hs).symm
      rw [hzs, hc', ← mul_assoc, inv_mul_cancel, one_mul]
      exact hz
    have h2 : ∀ z ∈ sylowCenter (S : Subgroup (XbarZ V H)), α z = z := by
      have hle : ⁅(S : Subgroup (XbarZ V H)), (S : Subgroup (XbarZ V H))⁆ ≤
          MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id (XbarZ V H)) := by
        rw [Subgroup.commutator_le]
        intro s hs t ht
        obtain ⟨z₁, hz₁, hαs₁⟩ := hαs s hs
        obtain ⟨z₂, hz₂, hαt₁⟩ := hαs t ht
        change α ⁅s, t⁆ = ⁅s, t⁆
        rw [map_commutatorElement, hαs₁, hαt₁]
        have c1 : ∀ x ∈ (S : Subgroup (XbarZ V H)), ∀ z ∈ sylowCenter (S : Subgroup (XbarZ V H)),
            Commute z x := fun x hx z hz => ((mem_sylowCenter.mp hz).2 x hx).symm
        exact commutator_mul_central (c1 s hs z₁ hz₁) (c1 t ht z₁ hz₁) (c1 z₂ (hZS hz₂) z₁ hz₁)
          (c1 s hs z₂ hz₂) (c1 t ht z₂ hz₂)
      intro z hz
      exact hle (hZc hz)
    obtain ⟨s₀, hs₀S, hαs₀⟩ := hAut α h1 h2 h3
    rw [← hSmap] at hs₀S
    obtain ⟨sb₀, hsb₀, hsb₀eq⟩ := hs₀S
    refine ⟨sb₀, hsb₀, ?_⟩
    apply hc.centralizes_of_tildeAut_eq_one hd
    intro x
    have hy : projZ V H (MulAut.conjNormal p x) = s₀ * projZ V H x * s₀⁻¹ := by
      have h' : α (projZ V H x) = projZ V H (MulAut.conjNormal p x) := tildeAut_mk p x
      rw [← h', hαs₀]
      rfl
    have hcx : (MulAut.conjNormal ((sb₀ : Hbar V H)⁻¹ * p) x : Xbar V H) =
        sb₀⁻¹ * MulAut.conjNormal p x * sb₀ := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcx, map_mul, map_mul, map_inv, hy, hsb₀eq]
    group
  set Sb' : Subgroup (Hbar V H) :=
    (Sb : Subgroup (Xbar V H)).map (barOf V H (xOf V H)).subtype with hSb'
  have hSb'2 : IsPGroup 2 Sb' := isPGroup_map_subtype Sb
  have hPb : ∀ p ∈ barOf V H P, ∀ y ∈ Sb', p * y * p⁻¹ ∈ Sb' := by
    intro p hp y hy
    obtain ⟨sb₀, hsb₀, hcc⟩ := hpc p hp
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨sb₀ * y' * sb₀⁻¹,
      (Sb : Subgroup (Xbar V H)).mul_mem ((Sb : Subgroup (Xbar V H)).mul_mem hsb₀ hy')
        ((Sb : Subgroup (Xbar V H)).inv_mem hsb₀), ?_⟩
    have hcy := hcc y'
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    calc (sb₀ : Hbar V H) * y' * (sb₀ : Hbar V H)⁻¹
        = (sb₀ : Hbar V H) * (((sb₀ : Hbar V H)⁻¹ * p) * y' * ((sb₀ : Hbar V H)⁻¹ * p)⁻¹) *
            (sb₀ : Hbar V H)⁻¹ := by rw [hcy]
      _ = p * y' * p⁻¹ := by group
  have hPN : barOf V H P ≤ Subgroup.normalizer (Sb' : Set (Hbar V H)) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hPb p hp y hy, fun hy => ?_⟩
    have := hPb p⁻¹ ((barOf V H P).inv_mem hp) _ hy
    simpa [mul_assoc] using this
  have hT2 : IsPGroup 2 ↥(barOf V H P ⊔ Sb') :=
    IsPGroup.to_sup_of_normal_right' hc.isPGroup_barOf_P hSb'2 hPN
  have hCV : wOf V H ⊓ Subgroup.centralizer (preimOf V H (barOf V H P ⊔ Sb') : Set G) ≤ V := by
    intro x hx
    have hPle : P ≤ preimOf V H (barOf V H P ⊔ Sb') := by
      intro g hg
      have hgH : g ∈ H := hc.PleH hg
      exact mem_preimOf.mpr ⟨⟨g, hgH⟩, rfl,
        Subgroup.mem_sup_left (mem_barOf_iff.mpr ⟨⟨g, hgH⟩, hg, rfl⟩)⟩
    have hxP : x ∈ Subgroup.centralizer (P : Set G) := Subgroup.centralizer_le hPle hx.2
    rw [hc.centralizer_P_eq] at hxP
    exact hxP
  intro n hn
  obtain ⟨x, hxn⟩ := xToZ_surjective hVH n
  have hb : xToXbar hVH x ∈ Subgroup.normalizer ((Sb : Subgroup (Xbar V H)) : Set (Xbar V H)) := by
    refine mem_normalizer_of_map_mem_normalizer (projZ V H)
      (le_of_eq (QuotientGroup.ker_mk' _)) Sb ?_
    rw [hSmap]
    have : projZ V H (xToXbar hVH x) = n := by rw [← xToZ_apply, hxn]
    rw [this]
    exact hn
  set b : Xbar V H := xToXbar hVH x with hbdef
  have hbSb : ∀ y ∈ (Sb : Subgroup (Xbar V H)), b * y * b⁻¹ ∈ (Sb : Subgroup (Xbar V H)) :=
    fun y hy => (Subgroup.mem_normalizer_iff.mp hb y).mp hy
  have hbT : (b : Hbar V H) ∈ Subgroup.normalizer
      ((barOf V H P ⊔ Sb' : Subgroup (Hbar V H)) : Set (Hbar V H)) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hle : conjSubgroup (b : Hbar V H) (barOf V H P ⊔ Sb') ≤ barOf V H P ⊔ Sb' := by
      unfold conjSubgroup
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨p, hp, rfl⟩
        obtain ⟨sb₀, hsb₀, hcc⟩ := hpc p hp
        have hcb : ((sb₀ : Hbar V H)⁻¹ * p) * (b : Hbar V H) =
            (b : Hbar V H) * ((sb₀ : Hbar V H)⁻¹ * p) := by
          have h0 := hcc b
          calc ((sb₀ : Hbar V H)⁻¹ * p) * (b : Hbar V H)
              = (((sb₀ : Hbar V H)⁻¹ * p) * (b : Hbar V H) * ((sb₀ : Hbar V H)⁻¹ * p)⁻¹) *
                ((sb₀ : Hbar V H)⁻¹ * p) := by group
            _ = (b : Hbar V H) * ((sb₀ : Hbar V H)⁻¹ * p) := by rw [h0]
        have hbc : (b : Hbar V H) * ((sb₀ : Hbar V H)⁻¹ * p) * (b : Hbar V H)⁻¹ =
            (sb₀ : Hbar V H)⁻¹ * p := by
          rw [← hcb]
          group
        have e : (MulAut.conj (b : Hbar V H)).toMonoidHom p =
            ((b * sb₀ * b⁻¹ : Xbar V H) : Hbar V H) * ((sb₀ : Hbar V H)⁻¹ * p) := by
          show (b : Hbar V H) * p * (b : Hbar V H)⁻¹ = _
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          calc (b : Hbar V H) * p * (b : Hbar V H)⁻¹
              = ((b : Hbar V H) * (sb₀ : Hbar V H) * (b : Hbar V H)⁻¹) *
                ((b : Hbar V H) * ((sb₀ : Hbar V H)⁻¹ * p) * (b : Hbar V H)⁻¹) := by group
            _ = _ := by rw [hbc]
        rw [e]
        have h1 : ((b * sb₀ * b⁻¹ : Xbar V H) : Hbar V H) ∈ Sb' :=
          Subgroup.mem_map.mpr ⟨_, hbSb sb₀ hsb₀, rfl⟩
        have h2 : (sb₀ : Hbar V H)⁻¹ ∈ Sb' :=
          Subgroup.mem_map.mpr ⟨sb₀⁻¹, (Sb : Subgroup (Xbar V H)).inv_mem hsb₀, rfl⟩
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hp))
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨b * y' * b⁻¹, hbSb y' hy', rfl⟩)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  rw [← hxn]
  exact hc.xToZ_mem_normalizer_of_isPGroup hT2 hCV hbT

theorem conj_mem_Rtilde (hc : MinCex M V Q P H) (hd : Sec23Data V H) {g : XbarZ V H}
    (hg : g ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H))) {r : XbarZ V H}
    (hr : r ∈ Rtilde V H P) : g * r * g⁻¹ ∈ Rtilde V H P := by
  obtain ⟨rb, hrb, rfl⟩ := Subgroup.mem_map.mp hr
  obtain ⟨gb, hgb⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) g
  have hgbg : projZ V H gb = g := hgb
  have hgbN : gb ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H)) :=
    hc.mem_normalizer_Vy_of_tilde hd (by rw [hgbg]; exact hg)
  obtain ⟨r', hr', hr'eq⟩ := hc.commutator_mem_Rbar hgbN (mem_Rbar.mp hrb)
  have hr'' : r' = gb * rb * gb⁻¹ * rb⁻¹ := Subtype.ext (by simpa using hr'eq)
  have hconj : g * projZ V H rb * g⁻¹ = projZ V H r' * projZ V H rb := by
    rw [hr'', map_mul, map_mul, map_mul, map_inv, map_inv, hgbg]
    group
  rw [hconj]
  exact Subgroup.mul_mem _ ⟨r', hr', rfl⟩ ⟨rb, hrb, rfl⟩

theorem normalizer_le_of_not_Rtilde_le (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hBG : IsBenderGroup (XbarZ V H)) (S : Sylow 2 (XbarZ V H))
    (hVS : VZ V H ≤ sylowCenter (S : Subgroup (XbarZ V H)))
    (hnR : ¬ Rtilde V H P ≤ sylowCenter (S : Subgroup (XbarZ V H)))
    (hcomm : ∀ r ∈ (S : Subgroup (XbarZ V H)), r ∉ sylowCenter (S : Subgroup (XbarZ V H)) →
      ∀ z ∈ sylowCenter (S : Subgroup (XbarZ V H)),
        ∃ s ∈ (S : Subgroup (XbarZ V H)), ⁅s, r⁆ = z)
    (hgen : ∀ R : Subgroup (XbarZ V H), R ≤ (S : Subgroup (XbarZ V H)) →
      sylowCenter (S : Subgroup (XbarZ V H)) < R →
      (∀ g ∈ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set (XbarZ V H)),
        (∀ z ∈ sylowCenter (S : Subgroup (XbarZ V H)), g * z = z * g) →
        ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      ∀ a : XbarZ V H, a ≠ 1 → a * a = 1 →
      a ∉ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set (XbarZ V H)) →
      R ⊔ Subgroup.zpowers a = ⊤) :
    ∀ n ∈ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set (XbarZ V H)),
      n ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
  have hVH : V ≤ H := hc.V_le_H
  have hE1 : VZ V H ≠ ⊥ := hc.Vtilde_ne_bot hd
  have hSN : ∀ s ∈ (S : Subgroup (XbarZ V H)),
      s ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := fun s hs =>
    mem_normalizer_VZ_of_le_sylowCenter hVS hs
  have hRS : Rtilde V H P ≤ (S : Subgroup (XbarZ V H)) :=
    hc.le_sylow_of_isPGroup hd hBG hVS hc.isPGroup_Rtilde hc.VZ_le_Rtilde
  obtain ⟨r, hrR, hrZ⟩ := SetLike.not_le_iff_exists.mp hnR
  have hZR : sylowCenter (S : Subgroup (XbarZ V H)) ≤ Rtilde V H P := by
    intro z hz
    obtain ⟨s, hsS, hsz⟩ := hcomm r (hRS hrR) hrZ z hz
    obtain ⟨rb, hrb, rfl⟩ := Subgroup.mem_map.mp hrR
    obtain ⟨sb, hsb⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) s
    have hsbN : sb ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H)) :=
      hc.mem_normalizer_Vy_of_tilde hd (by
        have : projZ V H sb = s := hsb
        rw [this]
        exact hSN s hsS)
    obtain ⟨r', hr', hr'eq⟩ := hc.commutator_mem_Rbar hsbN (mem_Rbar.mp hrb)
    have hr'' : r' = sb * rb * sb⁻¹ * rb⁻¹ := Subtype.ext (by simpa using hr'eq)
    refine ⟨r', hr', ?_⟩
    have : projZ V H sb = s := hsb
    rw [hr'', map_mul, map_mul, map_mul, map_inv, map_inv, this]
    simpa [commutatorElement_def] using hsz
  have hlt : sylowCenter (S : Subgroup (XbarZ V H)) < Rtilde V H P :=
    lt_of_le_not_ge hZR (fun h => hrZ (h hrR))
  obtain ⟨w, hw⟩ := exists_not_mem_normalizer hBG S
  obtain ⟨⟨v, hvE⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have ha₀E : w * v * w⁻¹ ∈ conjSubgroup w (VZ V H) := by
    rw [mem_conjSubgroup, show w⁻¹ * (w * v * w⁻¹) * w = v by group]
    exact hvE
  have ha₀1 : w * v * w⁻¹ ≠ 1 := by
    intro h
    apply hv1'
    have h2 : w⁻¹ * (w * v * w⁻¹) * w = 1 := by rw [h]; group
    rwa [show w⁻¹ * (w * v * w⁻¹) * w = v by group] at h2
  have ha₀N := not_mem_normalizer_of_mem_conj hBG hVS hw ha₀E ha₀1
  have ha₀sq : (w * v * w⁻¹) * (w * v * w⁻¹) = 1 := by
    have hvv := hc.VZ_sq hvE
    calc (w * v * w⁻¹) * (w * v * w⁻¹) = w * (v * v) * w⁻¹ := by group
      _ = 1 := by rw [hvv]; group
  have hnormR : ∀ g ∈ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set (XbarZ V H)),
      (∀ z ∈ sylowCenter (S : Subgroup (XbarZ V H)), g * z = z * g) →
      ∀ r ∈ Rtilde V H P, g * r * g⁻¹ ∈ Rtilde V H P := by
    intro g _ hgZ r hr
    refine hc.conj_mem_Rtilde hd ?_ hr
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hcen : ∀ u ∈ VZ V H, g * u * g⁻¹ = u := fun u hu => by
      rw [hgZ u (hVS hu)]
      group
    refine ⟨fun hu => by rw [hcen u hu]; exact hu, fun hu => ?_⟩
    have h1 : g * (g * u * g⁻¹) = (g * u * g⁻¹) * g := hgZ _ (hVS hu)
    have h2 : g⁻¹ * (g * u * g⁻¹) * g = g * u * g⁻¹ := by
      rw [mul_assoc, ← h1]
      group
    have h3 : u = g * u * g⁻¹ := by
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g * u * g⁻¹ := h2
    rwa [← h3] at hu
  have hgenR : Rtilde V H P ⊔ Subgroup.zpowers (w * v * w⁻¹) = ⊤ :=
    hgen _ hRS hlt hnormR _ ha₀1 ha₀sq ha₀N
  obtain ⟨r₀, a, hr₀, haV, y, hyD, hya, hπy⟩ := hc.exists_lift_conj hd ha₀E ha₀1
  set U : Subgroup G := Ugrp V H P with hU
  set K₀ : Subgroup (Xbar V H) :=
    (barOf V H (U ⊔ Subgroup.zpowers (a : G))).subgroupOf (barOf V H (xOf V H)) with hK₀
  have hyK₀ : y ∈ K₀ := by
    rw [hK₀, Subgroup.mem_subgroupOf, hya]
    exact mem_barOf_iff.mpr ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers (a : G)), rfl⟩
  have hRK : Rbar V H P ≤ K₀ := by
    intro r' hr'
    rw [hK₀, Subgroup.mem_subgroupOf]
    refine barOf_mono (le_sup_left : U ≤ U ⊔ Subgroup.zpowers (a : G)) ?_
    rw [hU, barOf_Ugrp]
    exact ⟨r', hr', rfl⟩
  have hmap : K₀.map (projZ V H) = ⊤ := by
    rw [eq_top_iff, ← hgenR]
    exact sup_le (Subgroup.map_mono hRK) (Subgroup.zpowers_le.mpr ⟨y, hyK₀, hπy⟩)
  have hker : (projZ V H).ker = Subgroup.center (Xbar V H) := QuotientGroup.ker_mk' _
  have hK : K₀ ⊔ Subgroup.center (Xbar V H) = ⊤ := by
    have h1 := Subgroup.comap_map_eq (projZ V H) K₀
    rw [hmap, Subgroup.comap_top, hker] at h1
    exact h1.symm
  have hgenX : xOf V H ≤ U ⊔ Subgroup.zpowers (a : G) :=
    xOf_le_sup_of_sup_center hd hVH (wOf_le_Ugrp V H P) hK ⟨y, hyD, hyK₀⟩
  have hFW : wOf V H ⊓ Subgroup.centralizer (U : Set G) ≤ wOf V H := inf_le_left
  have hFU : ∀ x ∈ wOf V H ⊓ Subgroup.centralizer (U : Set G), ∀ u ∈ U, x * u = u * x :=
    fun x hx u hu => (Subgroup.mem_centralizer_iff.mp hx.2 u hu).symm
  have hVF : V ⊓ wOf V H ≤ wOf V H ⊓ Subgroup.centralizer (U : Set G) := fun x hx =>
    ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun u hu => (hc.Ugrp_centralizes hx hu).symm⟩
  have hEq := hc.eq_inf_wOf_of_centralizes hFW hFU hVF r₀.2 haV hgenX
  have hCU : wOf V H ⊓ Subgroup.centralizer (U : Set G) ≤ V := fun x hx => by
    have hx' : x ∈ V ⊓ wOf V H := by rw [hEq]; exact hx
    exact hx'.1
  obtain ⟨Sb, hRSb, hSmap⟩ := hc.exists_sylow_over hd hBG hVS
  have hUS : U ≤ preimOf V H ((Sb : Subgroup (Xbar V H)).map (barOf V H (xOf V H)).subtype) :=
    preimOf_mono (Subgroup.map_mono hRSb)
  have hCV : wOf V H ⊓ Subgroup.centralizer
      (preimOf V H ((Sb : Subgroup (Xbar V H)).map (barOf V H (xOf V H)).subtype) : Set G) ≤ V :=
    fun x hx => hCU ⟨hx.1, Subgroup.centralizer_le hUS hx.2⟩
  intro n hn
  obtain ⟨x, hxn⟩ := xToZ_surjective hVH n
  have hb : xToXbar hVH x ∈ Subgroup.normalizer ((Sb : Subgroup (Xbar V H)) : Set (Xbar V H)) := by
    refine mem_normalizer_of_map_mem_normalizer (projZ V H)
      (le_of_eq (QuotientGroup.ker_mk' _)) Sb ?_
    rw [hSmap]
    have : projZ V H (xToXbar hVH x) = n := by rw [← xToZ_apply, hxn]
    rw [this]
    exact hn
  rw [← hxn]
  exact hc.xToZ_mem_normalizer_of_isPGroup (isPGroup_map_subtype Sb) hCV
    (mem_normalizer_map_subtype hb)

end MinCex

theorem tim79aIdentU3Statement_of_certs :
    Tim79aIdentU3Statement := by
  intro G _ _ M V Q P H hs _ _ hK
  obtain ⟨n, hn, ⟨e⟩⟩ := hK
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hd : Sec23Data V H := hs.data
  have hBG : IsBenderGroup (XbarZ V H) := .isPSU3 n hn e
  have hEel : Assembly.IsElemAbelian 2 (VZ V H) := hc.isElemAbelian_Vtilde
  have hE1 : VZ V H ≠ ⊥ := hc.Vtilde_ne_bot hd
  obtain ⟨S, hES⟩ := exists_le_sylowCenter hBG hEel
  have hN : ∀ m ∈ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set (XbarZ V H)),
      m ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
    by_cases hR : Rtilde V H P ≤ sylowCenter (S : Subgroup (XbarZ V H))
    · exact hc.normalizer_le_of_Rtilde_le hd hBG S hES hR (sylowCenter_le_commutator_psu3 hn e S)
        (fun φ h1 h2 h3 => aut_eq_conj_of_centralizes hBG S φ h1 h2 h3)
    · exact hc.normalizer_le_of_not_Rtilde_le hd hBG S hES hR
        (u3CommutatorOntoStatement_holds _ n hn ⟨e⟩ S)
        (u3NormalizedGenerationStatement_holds _ n hn ⟨e⟩ S)
  have hEZ : VZ V H = sylowCenter (S : Subgroup (XbarZ V H)) := by
    refine le_antisymm hES (fun z hz => ?_)
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    obtain ⟨m, hm, hzm⟩ := exists_normalizer_conj_mem hBG S hE1 hES hz hz1
    rwa [mem_normalizer_iff_conjSubgroup_eq.mp (hN m hm)] at hzm
  have hcard : Nat.card (VZ V H) = Nat.card (barOf V H V) := hc.card_Vtilde hd
  right
  right
  refine ⟨n, hn, ?_, ⟨e⟩, S, ?_⟩
  · rw [qBar, ← hcard, hEZ, card_sylowCenter_psu3 hn e S]
  · exact hEZ.trans (map_center_eq S).symm

theorem tim79aIdentBenderStatement_of_certs : Tim79aIdentBenderStatement :=
  tim79aIdentBenderStatement_of_parts tim79aIdentL2SzStatement_of_certs
    tim79aIdentU3Statement_of_certs

end CFSG.RankThree.GF2n.Tim79a
