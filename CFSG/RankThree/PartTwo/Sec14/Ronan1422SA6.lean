module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SExcl
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SPara2
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section KP4


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem K_bar_eq (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6)) :
    img148 A (Subgroup.normalizer (S : Set G)) (L ⊓ Subgroup.normalizer (R : Set G)) =
      img148 A (Subgroup.normalizer (S : Set G)) J := by
  refine Subgroup.eq_of_le_of_card_ge (img148_mono h.K_le) ?_
  rw [h.card_K_bar, Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num [Nat.factorial]

theorem exists_mem_B_of_commute_B (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6))
    {x : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸ ker148 A (Subgroup.normalizer (S : Set G))}
    (hx : ∀ b ∈ img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L), b * x = x * b) :
    ∃ b ∈ img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L),
      ∀ y ∈ img148 A (Subgroup.normalizer (S : Set G)) J, b⁻¹ * x * y = y * (b⁻¹ * x) := by
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set B' := img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L) with hB'
  obtain ⟨-, hB9, hBK⟩ := h.B_bar_facts
  have hBJ : B' ≤ J' := hBK.trans (img148_mono h.K_le)
  have hxN : x ∈ Subgroup.normalizer (J' : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact h.normal_J.conj_mem y hy x
    · intro hy
      have := h.normal_J.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this
  set α := J'.normalizerMonoidHom ⟨x, hxN⟩ with hα
  set β : MulAut (alternatingGroup (Fin 6)) := ψ.symm.trans (α.trans ψ) with hβ
  set B₀ : Subgroup (alternatingGroup (Fin 6)) := (B'.subgroupOf J').map ψ.toMonoidHom
    with hB₀
  have hB₀9 : Nat.card B₀ = 9 := by
    rw [hB₀, Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv, hB9]
  have hfix : ∀ b ∈ B₀, β b = b := by
    rintro _ ⟨b, hb, rfl⟩
    have hbB : (b : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))) ∈ B' := Subgroup.mem_subgroupOf.mp hb
    have hαb : α b = b := by
      apply Subtype.ext
      change x * (b : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))) * x⁻¹ = b
      rw [← hx _ hbB]
      group
    change ψ (α (ψ.symm (ψ b))) = ψ b
    rw [MulEquiv.symm_apply_apply, hαb]
  obtain ⟨b₀, hb₀, hβb₀⟩ := hA6.1 B₀ hB₀9 β hfix
  obtain ⟨b, hb, rfl⟩ := hb₀
  refine ⟨b, Subgroup.mem_subgroupOf.mp hb, fun y hy => ?_⟩
  have h1 : α ⟨y, hy⟩ = b * ⟨y, hy⟩ * b⁻¹ := by
    apply ψ.injective
    have := congrArg (fun γ : MulAut (alternatingGroup (Fin 6)) => γ (ψ ⟨y, hy⟩)) hβb₀
    simp only [hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
    rw [this, map_mul, map_mul, map_inv]
    rfl
  set bb : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸ ker148 A (Subgroup.normalizer (S : Set G)) :=
    ((b : ↥J') : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G))) with hbb
  have h2 : x * y * x⁻¹ = bb * y * bb⁻¹ := by
    have := congrArg Subtype.val h1
    simpa [hα, hbb] using this
  calc bb⁻¹ * x * y = bb⁻¹ * (x * y * x⁻¹) * x := by group
    _ = bb⁻¹ * (bb * y * bb⁻¹) * x := by rw [h2]
    _ = y * (bb⁻¹ * x) := by group

theorem le_centralizer_J_of_two (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6))
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    img148 A (Subgroup.normalizer (S : Set G)) T ≤
      Subgroup.centralizer (img148 A (Subgroup.normalizer (S : Set G)) J :
        Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
          ker148 A (Subgroup.normalizer (S : Set G)))) := by
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set B' := img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L) with hB'
  set T' := img148 A (Subgroup.normalizer (S : Set G)) T with hT'
  obtain ⟨-, hB9, hBK⟩ := h.B_bar_facts
  have hBJ : B' ≤ J' := hBK.trans (img148_mono h.K_le)
  have hN : ∀ x, x ∈ Subgroup.normalizer (J' : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)))) := by
    intro x
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_J]
    exact Subgroup.mem_top x
  let ι : ↥T' →* MulAut ↥J' := J'.normalizerMonoidHom.comp
    (Subgroup.inclusion (fun x _ => hN x))
  set Q : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    ι.range.map (MulAut.congr ψ).toMonoidHom with hQ
  have hT'2 : IsPGroup 2 T' := (hT2.comap_subtype (K := Subgroup.normalizer (S : Set G) ⊔ A)).map _
  have hQ2 : IsPGroup 2 Q := by
    have : IsPGroup 2 ι.range := by
      rw [MonoidHom.range_eq_map]
      exact (hT'2.of_equiv (Subgroup.topEquiv).symm).map ι
    exact this.map _
  set B₀ : Subgroup (alternatingGroup (Fin 6)) := (B'.subgroupOf J').map ψ.toMonoidHom
    with hB₀
  have hB₀9 : Nat.card B₀ = 9 := by
    rw [hB₀, Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv, hB9]
  have hBT : B' ≤ Subgroup.normalizer (T' : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)))) :=
    img148_le_normalizer (inf_le_left.trans hAT)
  have hQn : ∀ b ∈ B₀, ∀ q ∈ Q, MulAut.conj b * q * (MulAut.conj b)⁻¹ ∈ Q := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have hbB : (b : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))) ∈ B' := Subgroup.mem_subgroupOf.mp hb
    have hbt : (b : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))) * t * (b : _)⁻¹ ∈ T' :=
      (Subgroup.mem_normalizer_iff.mp (hBT hbB) t).mp t.2
    refine ⟨ι ⟨_, hbt⟩, ⟨⟨_, hbt⟩, rfl⟩, ?_⟩
    apply MulEquiv.ext
    intro a
    apply ψ.symm.injective
    apply Subtype.ext
    simp [ι, MulAut.congr_apply, MulAut.conj_apply, mul_assoc]
  have hQbot := hA6.2.1 B₀ hB₀9 Q hQ2 hQn
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hι : ι ⟨t, ht⟩ = 1 := by
    have hmem : (MulAut.congr ψ) (ι ⟨t, ht⟩) ∈ Q := ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
    rw [hQbot, Subgroup.mem_bot] at hmem
    exact (MulEquiv.map_eq_one_iff _).mp hmem
  have := congrArg (fun γ : MulAut ↥J' => ((γ ⟨y, hy⟩ : ↥J') : ↥(Subgroup.normalizer (S : Set G) ⊔
    A) ⧸ ker148 A (Subgroup.normalizer (S : Set G)))) hι
  simp only [ι, MonoidHom.comp_apply, MulAut.one_apply] at this
  change t * y * t⁻¹ = y at this
  calc y * t = t * y * t⁻¹ * t := by rw [this]
    _ = t * y := by group

theorem eq_bot_of_normal_coprime (h : Cfg A c L R S J)
    {N : Subgroup (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)))} (hN : N.Normal)
    (hN3 : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  set π := QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) with hπ
  set P := N.comap π with hP
  have hPn : P.Normal := hN.comap π
  have hPcard : Nat.card P =
      Nat.card (ker148 A (Subgroup.normalizer (S : Set G))) * Nat.card N := by
    have h1 := QuotientGroup.card_preimage_mk (ker148 A (Subgroup.normalizer (S : Set G)))
      (N : Set _)
    exact h1
  have hP3 : Nat.Coprime 3 (Nat.card P) := by
    rw [hPcard]
    refine Nat.Coprime.mul_right ?_ hN3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr Main148.not_three_dvd_card_ker148
  have hPle : P ≤ CFSG.pPrimeCore 3 ↥(Subgroup.normalizer (S : Set G) ⊔ A) := le_sSup ⟨hPn, hP3⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hm : m ∈ CFSG.pPrimeCore 3 ↥(Subgroup.normalizer (S : Set G) ⊔ A) := hPle hx
  rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
  have h1 : (m : G) ∈ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G) ⊔ A) := ⟨m, hm, rfl⟩
  have heq : pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G) ⊔ A) =
      pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) := congrArg (pPrimeCoreOf 3) h.sup_A_eq
  rwa [heq] at h1

theorem le_pPrimeCoreOf_of_two (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* alternatingGroup (Fin 6))
    {T : Subgroup G} (hTM : T ≤ Subgroup.normalizer (S : Set G)) (hT2 : IsPGroup 2 T)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) := by
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set B := A ⊓ L with hBdef
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set Q := Subgroup.normalizer (S : Set G) ⊔ A with hQ
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set B' := img148 A (Subgroup.normalizer (S : Set G)) B with hB'
  set Z := Subgroup.centralizer (J' : Set (↥Q ⧸ ker148 A (Subgroup.normalizer (S : Set G))))
    with hZ
  obtain ⟨hBe, -, hBK⟩ := h.B_bar_facts
  have hBJ : B' ≤ J' := hBK.trans (img148_mono h.K_le)
  have hTQ : T ≤ Q := hTM.trans le_sup_left
  have hACB : A ≤ Subgroup.normalizer (CB : Set G) := by
    refine le_trans ?_ Subgroup.le_normalizer
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨b, hb.1⟩ ⟨a, ha⟩)
  have hTZ := h.le_centralizer_J_of_two hA6 ψ hT2 hAT
  have hTB : img148 A (Subgroup.normalizer (S : Set G)) T ≤
      Subgroup.centralizer (B' : Set (↥Q ⧸ ker148 A (Subgroup.normalizer (S : Set G)))) :=
    hTZ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBJ))
  have hD3 := img148_inf_centralizer_of_le h.A_le_NM hA3 (inf_le_left : B ≤ A) hTQ hAT
  rw [inf_eq_left.mpr hTB] at hD3
  have hTCB : T ⊓ CB ≤ pPrimeCoreOf 3 CB :=
    h.pt.le_pPrimeCoreOf_centralizer_B (hT2.to_le inf_le_left)
      (Late.le_normalizer_inf hAT hACB) inf_le_right
  set Y := pPrimeCoreOf 3 CB ⊓ Q with hY
  set Y' := img148 A (Subgroup.normalizer (S : Set G)) Y with hY'
  have hTY : img148 A (Subgroup.normalizer (S : Set G)) T ≤ Y' := by
    rw [hD3]
    exact img148_mono (le_inf hTCB (inf_le_left.trans hTQ))
  have hY3 : Nat.Coprime 3 (Nat.card Y') :=
    Nat.Coprime.coprime_dvd_right ((Main148.card_img148_dvd inf_le_right).trans
      (Subgroup.card_dvd_of_le inf_le_left)) (coprime_card_pPrimeCoreOf 3 CB)
  have hYB : ∀ y ∈ Y', ∀ b ∈ B', b * y = y * b := by
    intro y hy b hb
    obtain ⟨g, hg, hgY, rfl⟩ := mem_img148_iff.mp hy
    obtain ⟨d, hd, hdB, rfl⟩ := mem_img148_iff.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp ((pPrimeCoreOf_le 3 CB) hgY.1) d hdB
  have hYZ : Y' ≤ Z := by
    intro y hy
    obtain ⟨b, hb, hbz⟩ := h.exists_mem_B_of_commute_B hA6 ψ (hYB y hy)
    set z := b⁻¹ * y with hzdef
    have hzZ : z ∈ Z := Subgroup.mem_centralizer_iff.mpr fun j hj => (hbz j hj).symm
    have hbz' : b * z = z * b := Subgroup.mem_centralizer_iff.mp hzZ b (hBJ hb)
    set m := orderOf y with hm
    have hm3 : Nat.Coprime 3 m :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Y' hy) hY3
    have hy1 : y ^ m = 1 := pow_orderOf_eq_one y
    have hyb : y = b * z := by rw [hzdef]; group
    have hbm : b ^ m = (z ^ m)⁻¹ := by
      rw [hyb, (Commute.mul_pow hbz' m)] at hy1
      exact eq_inv_of_mul_eq_one_left hy1
    have hbmZ : b ^ m ∈ Z := by rw [hbm]; exact Z.inv_mem (Z.pow_mem hzZ m)
    have hbm1 : b ^ m = 1 :=
      h.eq_one_of_mem_B_of_commute (B'.pow_mem hb m) fun k hk =>
        (Subgroup.mem_centralizer_iff.mp hbmZ k (img148_mono h.K_le hk))
    have hb3 : b ^ 3 = 1 := hBe.2 b hb
    have hb1 : b = 1 := by
      have : b ^ Nat.gcd 3 m = 1 := pow_gcd_eq_one.mpr ⟨hb3, hbm1⟩
      rwa [Nat.Coprime.gcd_eq_one hm3, pow_one] at this
    rw [hyb, hb1, one_mul]
    exact hzZ
  have hZN : Z ≤
      Subgroup.normalizer (Y' : Set (↥Q ⧸ ker148 A (Subgroup.normalizer (S : Set G)))) := by
    have hD3' := img148_inf_centralizer_of_le h.A_le_NM hA3 (inf_le_left : B ≤ A) le_rfl
      (le_sup_right.trans Subgroup.le_normalizer : A ≤ Subgroup.normalizer (Q : Set G))
    have htop : img148 A (Subgroup.normalizer (S : Set G)) Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact mem_img148_iff.mpr ⟨m, m.2, m.2, rfl⟩
    rw [htop, top_inf_eq] at hD3'
    intro z hz
    have hzB : z ∈ Subgroup.centralizer (B' : Set (↥Q ⧸ ker148 A (Subgroup.normalizer (S : Set G))))
      := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBJ) hz
    rw [hD3'] at hzB
    refine img148_le_normalizer ?_ hzB
    intro x hx
    exact mem_normalizer_inf (le_normalizer_pPrimeCoreOf 3 CB hx.2)
      (Subgroup.le_normalizer hx.1)
  haveI : J'.Normal := h.normal_J
  have hYc : Y' ≤ pPrimeCoreOf 3 Z := by
    have hn : (Y'.subgroupOf Z).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYZ).mpr hZN
    have hc : Nat.Coprime 3 (Nat.card (Y'.subgroupOf Z)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYZ).toEquiv]
    have hle : Y'.subgroupOf Z ≤ CFSG.pPrimeCore 3 ↥Z := le_sSup ⟨hn, hc⟩
    intro y hy
    exact ⟨⟨y, hYZ hy⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hOn : (pPrimeCoreOf 3 Z).Normal := by
    unfold pPrimeCoreOf
    infer_instance
  have hO3 : Nat.Coprime 3 (Nat.card (pPrimeCoreOf 3 Z)) := coprime_card_pPrimeCoreOf 3 Z
  have hYbot : Y' = ⊥ := le_bot_iff.mp (h.eq_bot_of_normal_coprime hOn hO3 ▸ hYc)
  intro t ht
  have hmem : QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) ⟨t, hTQ ht⟩ ∈ Y' :=
    hTY (mem_img148_iff.mpr ⟨t, hTQ ht, ht, rfl⟩)
  rw [hYbot, Subgroup.mem_bot, mk'_ker148_eq_one_iff] at hmem
  exact hmem

end Cfg

end KP4

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
