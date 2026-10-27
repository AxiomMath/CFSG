module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Package
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RankBound
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBSylow
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LNormalizer
public import CFSG.Mathlib.GroupTheory.OddInvariantSylow

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem mem_normalizer_centralizer {G : Type} [Group G] [Finite G] {B : Subgroup G}
    {g : G} (h : ∀ x ∈ B, g * x * g⁻¹ ∈ B) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  simp only [SetLike.mem_coe] at hy ⊢
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro x hx
  have hxB : g⁻¹ * x * g ∈ B := GGFF.inv_conj_mem_of_conj_mem h hx
  have hyc : (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g) := hy (g⁻¹ * x * g) hxB
  calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hyc]
    _ = (g * y * g⁻¹) * x := by group

private theorem mem_normalizer_zpowers_of_mul_comm {G : Type} [Group G] [Finite G] {x t : G}
    (h : x * t = t * x) : x ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  have hxt : (MulAut.conj x) t = t := by
    rw [MulAut.conj_apply, h, mul_inv_cancel_right]
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx : x * t ^ k * x⁻¹ = t ^ k := by
    have : (MulAut.conj x) (t ^ k) = t ^ k := by rw [map_zpow, hxt]
    simpa [MulAut.conj_apply] using this
  rw [hx]
  exact Subgroup.zpow_mem_zpowers t k

theorem odd_cen_b2 {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    (hB₂ : B2Package b z B₂) : Odd (Nat.card ↥(Subgroup.centralizer (B₂ : Set G))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨t, ht⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (B₂ : Set G))) 2 hodd
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htGne : (t : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htG
    omega
  have hTne : Subgroup.zpowers (t : G) ≠ ⊥ := by
    intro hbot
    have : (t : G) ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers (t : G)
    exact htGne (Subgroup.mem_bot.mp this)
  have hT2 : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htG]; norm_num)
  have hle : B₂ ≤ Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := fun x hx =>
    mem_normalizer_zpowers_of_mul_comm (Subgroup.mem_centralizer_iff.mp t.2 x hx)
  have hbound := card_le_of_normalizer_isPGroup_two h.hypA h.model hTne hT2 hle hB₂.abel
  rw [hB₂.card] at hbound
  norm_num at hbound

structure AStarBase {G : Type} [Group G] (b : G) {L : Subgroup G} (z : Fin 3 → ↥L)
    (B₂ A : Subgroup G) : Prop where
  le_cen : A ≤ Subgroup.centralizer (B₂ : Set G)
  isP : IsPGroup 3 A
  max : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (B₂ : Set G) → IsPGroup 3 P → A ≤ P → P = A
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  B₂_le : B₂ ≤ A
  nor : ∀ g ∈ dGrp b z, ∀ x ∈ A, g * x * g⁻¹ ∈ A
  cen_b : ∀ x ∈ A, x * b = b * x → x ∈ bOne z

theorem exists_aStarBase {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    (hB₂ : B2Package b z B₂) : ∃ A : Subgroup G, AStarBase b z B₂ A := by
  have hYodd : Odd (Nat.card ↥(Subgroup.centralizer (B₂ : Set G))) := odd_cen_b2 h hB₂
  have hDleN : dGrp b z ≤
      Subgroup.normalizer (Subgroup.centralizer (B₂ : Set G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_centralizer hB₂.b_nor
    · intro g hg
      exact mem_normalizer_centralizer (hB₂.D_nor g hg)
  obtain ⟨S, hSleY, hSp, hSmax, hSnor⟩ :=
    CFSG.OddInvariantSylow.exists_isPGroup_normalizer
      (Y := Subgroup.centralizer (B₂ : Set G)) (D := dGrp b z)
      hYodd hDleN (isSolvable_dGrp h) (prime_eq_two_or_three_of_dvd_dGrp h)
  have hB₂Y : B₂ ≤ Subgroup.centralizer (B₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hB₂.abel.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hB₂P : IsPGroup 3 B₂ := IsPGroup.of_card (n := 6) (by rw [hB₂.card])
  have hB₂norS : B₂ ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hcomm : y * x = x * y := (Subgroup.mem_centralizer_iff.mp (hSleY hy) x hx).symm
    have : x * y * x⁻¹ = y := by rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hy
  have hB₂leS : B₂ ≤ S := by
    have hsupP : IsPGroup 3 ↥(S ⊔ B₂) := IsPGroup.to_sup_of_normal_left' hSp hB₂P hB₂norS
    have hsup_eq : S ⊔ B₂ = S :=
      hSmax (S ⊔ B₂) (sup_le hSleY hB₂Y) hsupP le_sup_left
    intro x hx
    exact hsup_eq ▸ (Subgroup.mem_sup_right hx : x ∈ S ⊔ B₂)
  obtain ⟨τ, c, hτc⟩ := exists_tauC h
  have hτnorB₁ : τ ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => by
      rw [hB₂.tau_inv τ hτc.tau_mem hτc.inv x (hB₂.B₁_le hx)]
      exact (bOne z).inv_mem hx
  have hτD : τ ∈ dGrp b z := Subgroup.mem_sup_right ⟨hτc.tau_mem, hτnorB₁⟩
  have hτnorS : τ ∈ Subgroup.normalizer (S : Set G) := hSnor hτD
  have hτconj : ∀ x ∈ S, τ * x * τ⁻¹ ∈ S := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hτnorS x).mp hx
  have hcenb : ∀ x ∈ S, x * b = b * x → x ∈ bOne z := by
    intro x hxS hxb
    have hxY : x ∈ Subgroup.centralizer (B₂ : Set G) := hSleY hxS
    have hxB₂ : ∀ v ∈ B₂, v * x = x * v := fun v hv =>
      Subgroup.mem_centralizer_iff.mp hxY v hv
    have hxC : x ∈ cB b z := by
      rw [cB]
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have hleBt : GGFF.Bt b z ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [GGFF.Bt]
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr hxb.symm
        · rw [GGFF.tor]
          refine (Subgroup.closure_le _).mpr ?_
          rintro _ ⟨i, rfl⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (hxB₂ _ (hB₂.B₁_le (Subgroup.subset_closure ⟨i, rfl⟩)))
      have := hleBt hw
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    have hx3 : IsPGroup 3 (Subgroup.zpowers x) := hSp.to_le (Subgroup.zpowers_le.mpr hxS)
    have hxB : x ∈ GGFF.Bt b z := mem_Bt_of_isPGroup_cen h x hxC hx3
    obtain ⟨j, v, hxv⟩ := h.settingCore.mem_Bt.mp hxB
    have hvB₂ : vecElt (GGFF.zs z) v ∈ B₂ :=
      hB₂.B₁_le (GGFF.vecElt_mem_tor (GGFF.zs z) v)
    have hbjY : b ^ j ∈ Subgroup.centralizer (B₂ : Set G) := by
      have hw : vecElt (GGFF.zs z) v ∈ Subgroup.centralizer (B₂ : Set G) := hB₂Y hvB₂
      have : b ^ j = x * (vecElt (GGFF.zs z) v)⁻¹ := by rw [hxv]; group
      rw [this]
      exact (Subgroup.centralizer (B₂ : Set G)).mul_mem hxY
        ((Subgroup.centralizer (B₂ : Set G)).inv_mem hw)
    by_cases hbj1 : b ^ j = 1
    · rw [hxv, hbj1, one_mul]
      exact GGFF.vecElt_mem_tor (GGFF.zs z) v
    · exfalso
      have hbz : b ∈ Subgroup.zpowers (b ^ j) := by
        rcases GGFF.eq_or_eq_inv_of_mem_zpowers h.hypA.ord
          (Subgroup.zpow_mem_zpowers b j) hbj1 with he | he
        · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one, he]⟩
        · exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp [he]⟩
      have hbY : b ∈ Subgroup.centralizer (B₂ : Set G) := Subgroup.zpowers_le.mpr hbjY hbz
      have hB₂_le_bOne : B₂ ≤ bOne z := fun y hy =>
        hB₂.fix y hy (Subgroup.mem_centralizer_iff.mp hbY y hy)
      have hdvd : Nat.card B₂ ∣ Nat.card (bOne z) := Subgroup.card_dvd_of_le hB₂_le_bOne
      rw [hB₂.card, show Nat.card (bOne z) = 27 from h.settingCore.card_torG] at hdvd
      have := Nat.le_of_dvd (by norm_num : 0 < 27) hdvd
      norm_num at this
  have hbτ : τ * b = b * τ :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.tau_mem)
  have hbS : b ∈ Subgroup.normalizer (S : Set G) :=
    hSnor (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have hbF : b ∈ Subgroup.normalizer (S ⊓ Subgroup.centralizer ({τ} : Set G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hbS (y : G)).mp hy.1
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hyτ : (y : G) * τ = τ * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hy.2
      have hτconj : b * τ * b⁻¹ = τ := by
        rw [hbτ.symm, mul_assoc, mul_inv_cancel, mul_one]
      calc b * (y : G) * b⁻¹ * τ
          = b * (y : G) * b⁻¹ * (b * τ * b⁻¹) := by rw [hτconj]
        _ = b * ((y : G) * τ) * b⁻¹ := by group
        _ = b * (τ * (y : G)) * b⁻¹ := by rw [hyτ]
        _ = (b * τ * b⁻¹) * (b * (y : G) * b⁻¹) := by group
        _ = τ * (b * (y : G) * b⁻¹) := by rw [hτconj]
  have hFbot : S ⊓ Subgroup.centralizer ({τ} : Set G) = ⊥ := by
    by_contra hFne
    let F : Subgroup G := S ⊓ Subgroup.centralizer ({τ} : Set G)
    have hFne' : F ≠ ⊥ := hFne
    have hbF' : b ∈ Subgroup.normalizer (F : Set G) := hbF
    have hle' : Subgroup.zpowers b ≤ Subgroup.normalizer (F : Set G) :=
      Subgroup.zpowers_le.mpr hbF'
    let act : MulAction ↥(Subgroup.zpowers b) ↥F :=
      MulAction.compHom ↥F (Subgroup.inclusion hle')
    have hFp : IsPGroup 3 F := hSp.to_le inf_le_left
    have hFnt : Nontrivial ↥F := (Subgroup.nontrivial_iff_ne_bot F).mpr hFne'
    have h3dvd : 3 ∣ Nat.card ↥F := by
      obtain ⟨k, hk0, hk⟩ := hFp.nontrivial_iff_card.mp hFnt
      rw [hk]
      exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hk0)
    have hGb : IsPGroup 3 ↥(Subgroup.zpowers b) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hypA.ord]; norm_num)
    have h1fix : (1 : ↥F) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers b) ↥F := by
      intro g
      change (Subgroup.inclusion hle' g) • (1 : ↥F) = (1 : ↥F)
      exact Subtype.ext (by simp)
    obtain ⟨x, hxfix, hxne⟩ :=
      hGb.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥F) h3dvd h1fix
    have hxfixb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) • x = x := hxfix _
    have hbx : b * (x : G) * b⁻¹ = (x : G) := by
      have h := hxfixb
      rw [MulAction.compHom_smul_def] at h
      exact congrArg Subtype.val h
    have hxb : (x : G) * b = b * (x : G) := by
      calc (x : G) * b = (b * (x : G) * b⁻¹) * b := by rw [hbx]
        _ = b * (x : G) := by group
    have hxB₁ : (x : G) ∈ bOne z := hcenb (x : G) x.2.1 hxb
    have hxτ : (x : G) * τ = τ * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    have hτx : τ * (x : G) * τ⁻¹ = (x : G) := by
      rw [← hxτ, mul_assoc, mul_inv_cancel, mul_one]
    have hτinv : τ * (x : G) * τ⁻¹ = (x : G)⁻¹ :=
      hB₂.tau_inv τ hτc.tau_mem hτc.inv (x : G) (hB₂.B₁_le hxB₁)
    have hx_inv : (x : G) = (x : G)⁻¹ := by rw [← hτinv, hτx]
    have hsq : (x : G) * (x : G) = 1 := by
      have h : (x : G) * (x : G) = (x : G) * (x : G)⁻¹ :=
        congrArg (fun z => (x : G) * z) hx_inv
      simpa using h
    have hx3 : (x : G) ^ 3 = 1 := hB₂.abel.2 (x : G) (hB₂.B₁_le hxB₁)
    have hx1 : (x : G) = 1 := by
      calc (x : G) = (x : G) ^ 3 * ((x : G) * (x : G))⁻¹ := by group
        _ = 1 := by rw [hx3, hsq, inv_one, mul_one]
    exact hxne (Subtype.ext (by simpa using hx1.symm))
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    let φ : ↥S →* ↥S :=
      { toFun := fun x => ⟨τ * (x : G) * τ⁻¹, hτconj (x : G) x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          group) }
    have hfpf : MonoidHom.FixedPointFree φ := by
      intro x hx
      have hxG : τ * (x : G) * τ⁻¹ = (x : G) := congrArg Subtype.val hx
      have hxF : (x : G) ∈ S ⊓ Subgroup.centralizer ({τ} : Set G) := by
        refine ⟨x.2, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc (x : G) * τ = (τ * (x : G) * τ⁻¹) * τ := by rw [hxG]
            _ = τ * (x : G) := by group)
      exact Subtype.ext (Subgroup.mem_bot.mp (hFbot ▸ hxF))
    have hinvol : Function.Involutive φ := fun x => Subtype.ext (by
      show τ * (τ * (x : G) * τ⁻¹) * τ⁻¹ = (x : G)
      have hττ : τ * τ = 1 := by simpa [pow_two] using hτc.tau_sq
      have h1 : τ⁻¹ * τ⁻¹ = 1 := by rw [← mul_inv_rev, hττ, inv_one]
      rw [show τ * (τ * (x : G) * τ⁻¹) * τ⁻¹ = (τ * τ) * (x : G) * (τ⁻¹ * τ⁻¹)
        by group, hττ, h1]
      simp)
    intro x hxS y hyS
    exact congrArg Subtype.val
      (hfpf.commute_all_of_involutive hinvol ⟨x, hxS⟩ ⟨y, hyS⟩).eq
  refine ⟨S, ?_⟩
  exact
    { le_cen := hSleY
      isP := hSp
      max := hSmax
      comm := hcomm
      B₂_le := hB₂leS
      nor := fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hSnor hg) x).mp hx
      cen_b := hcenb }

end CFSG.StandardType.FF81.PropOne

end
