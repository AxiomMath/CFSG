module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoConclusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open CFSG.Blueprint Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem index_le_two_and_surj_of_setting {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hK : Nat.card K = 4) {L : Subgroup G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (S : CFSG.LargeExtraspecial.Setting G) (hw : S.width = 10) (hLM : L ≤ S.M)
    (hLQ : L ⊓ S.QG = ⊥) (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    (hU12 : ¬ Nonempty (G ≃* timmesfeldPSU 12)) :
    (timmesfeldFStar S.Mbar).index ≤ 2 ∧
      ∀ y ∈ timmesfeldFStar S.Mbar, ∃ l : L, S.ρ ⟨(l : G), hLM l.2⟩ = (y : S.O) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKU : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI hfinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI hsimpleU : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hKU 6 (by norm_num)
      (by norm_num)
  haveI hsimpleL : IsSimpleGroup L := MulEquiv.isSimpleGroup φ
  haveI hperfU : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    haveI : Group.IsPerfect ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) hKU (n := 6)
        (by norm_num) (by norm_num)
    exact Group.IsPerfect.ofSurjective
      (f := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (QuotientGroup.mk'_surjective _)
  haveI hperfL : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective
      (f := (φ.symm : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* L))
      φ.symm.surjective
  have h11L : 11 ∣ Nat.card L := by
    rw [Nat.card_congr φ.toEquiv]
    change 11 ∣ Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K))
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := 1) (n := 6)
      Nat.prime_two le_rfl hKU (by norm_num)]
    decide
  have h11PSL : ¬ 11 ∣ Nat.card (PSL(6, ZMod 2)) := by
    change ¬ 11 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 6) (ZMod 2))
    rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear (ZMod 2) 6 (by norm_num),
      Nat.card_eq_fintype_card, ZMod.card]
    decide
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    have hnc : ¬ ∀ x y : L, x * y = y * x := by
      intro h
      exact Group.IsPerfect.not_isMulCommutative L ⟨⟨h⟩⟩
    by_contra hcon
    push Not at hcon
    exact hnc fun x y => Subtype.ext (hcon (x : G) (y : G))
  obtain ⟨a, b, hab⟩ := hnonab
  have h := (CFSG.LargeExtraspecial.Bridge.orderMainFor_iff G).mp hT ⟨a, b, hab⟩ S
  rw [hw] at h
  rw [CFSG.LargeExtraspecial.Bridge.timmesfeldOrderConclusion_iff] at h
  let ι : L →* S.Mbar := S.ρ.rangeRestrict.comp (Subgroup.inclusion hLM)
  have hιker : ι.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxρ : S.ρ ⟨x, hLM x.2⟩ = 1 := by
        have h1 : ((ι x : S.Mbar) : S.O) = 1 := by rw [hx]; rfl
        exact h1
      have hxQ : (x : G) ∈ S.QG :=
        S.mem_QG_iff.mpr ⟨hLM x.2, by rw [← S.ker_ρ, MonoidHom.mem_ker]; exact hxρ⟩
      have hxbot : (x : G) ∈ L ⊓ S.QG := ⟨x.2, hxQ⟩
      rw [hLQ] at hxbot
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    · intro hx
      rw [hx, map_one ι]
  have hιinj : Function.Injective ι := (MonoidHom.ker_eq_bot_iff ι).mp hιker
  rcases h with h1 | (h2a | h2b) | h3 | h4 | h5 | h6 | h7 | h8
  · exfalso; omega
  · exact absurd (show Nonempty (G ≃* PSL(12, ZMod 2)) from h2a)
      (not_nonempty_mulEquiv_psl12 hK φ)
  · exact absurd (show Nonempty (G ≃* timmesfeldPSU 12) from h2b) hU12
  · exfalso
    obtain ⟨-, -, q, -, hcase⟩ := h3
    have hcard1024 : Nat.card (Fin 10 → ZMod 2) = 1024 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have key : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (X : Subgroup (V ≃ₗ[ZMod 2] V)) (e : S.Mbar ≃* (Equiv.Perm (Fin 3) × X)),
        Nat.card V = 1024 → False := by
      intro V _ _ _ X e hV
      let f : S.Mbar →* (V ≃ₗ[ZMod 2] V) :=
        X.subtype.comp ((MonoidHom.snd (Equiv.Perm (Fin 3)) X).comp e.toMonoidHom)
      let g : L →* (V ≃ₗ[ZMod 2] V) := f.comp ι
      rcases hsimpleL.eq_bot_or_eq_top_of_normal g.ker with hbot | htop
      · have hginj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hbot
        have hψinj : Function.Injective (g.comp φ.symm.toMonoidHom) := by
          intro x y hxy
          exact φ.symm.injective (hginj hxy)
        have h20 := twenty_le_finrank_of_injective (V := V) hK (g.comp φ.symm.toMonoidHom) hψinj
        have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
        have h2 : 2 ^ 20 ≤ Nat.card V := by
          rw [hcard]
          exact Nat.pow_le_pow_right (by norm_num) h20
        rw [hV] at h2
        norm_num at h2
      · have htop2 : ∀ x : L, (e (ι x)).2 = 1 := by
          intro x
          have hmem : x ∈ g.ker := by rw [htop]; exact Subgroup.mem_top x
          have h1 : g x = 1 := by simpa using hmem
          have h2 : X.subtype ((e (ι x)).2) = X.subtype 1 := by
            simpa [g, f, MonoidHom.comp_apply] using h1
          exact X.subtype_injective h2
        let p : L →* Equiv.Perm (Fin 3) :=
          (MonoidHom.fst (Equiv.Perm (Fin 3)) X).comp (e.toMonoidHom.comp ι)
        have hpinj : Function.Injective p := by
          intro x y hxy
          have hxy' : (e (ι x)).1 = (e (ι y)).1 := hxy
          have h1 : e (ι x) = e (ι y) := by
            refine Prod.ext hxy' ?_
            rw [htop2 x, htop2 y]
          exact hιinj (e.injective h1)
        have hcard : Nat.card L ≤ Nat.card (Equiv.Perm (Fin 3)) :=
          Nat.card_le_card_of_injective p hpinj
        have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
          norm_num
        rw [hcard6] at hcard
        have h11 : 11 ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos h11L
        omega
    rcases hcase with h | h
    · obtain ⟨e⟩ := h
      exact key _ e hcard1024
    · obtain ⟨e⟩ := h
      exact key _ e hcard1024
  · exfalso; obtain ⟨h, -⟩ := h4; omega
  · obtain ⟨-, hidx, hF⟩ := h5
    refine ⟨hidx, ?_⟩
    haveI hFnormal : (timmesfeldFStar S.Mbar).Normal := by
      rw [← CFSG.LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar]
      exact (CFSG.LocalCores.generalized_fitting_characteristic).2
    let q : S.Mbar →* (S.Mbar ⧸ timmesfeldFStar S.Mbar) := QuotientGroup.mk' _
    let g : L →* (S.Mbar ⧸ timmesfeldFStar S.Mbar) := q.comp ι
    rcases hsimpleL.eq_bot_or_eq_top_of_normal g.ker with hbot | htop
    · exfalso
      have hginj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hbot
      have hqcard : Nat.card (S.Mbar ⧸ timmesfeldFStar S.Mbar) ≤ 2 := by
        rw [← Subgroup.index_eq_card]
        exact hidx
      have hle : Nat.card L ≤ Nat.card (S.Mbar ⧸ timmesfeldFStar S.Mbar) :=
        Nat.card_le_card_of_injective g hginj
      have h11 : 11 ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos h11L
      omega
    · have hleF : ι.range ≤ timmesfeldFStar S.Mbar := by
        rintro _ ⟨x, rfl⟩
        have hmem : x ∈ g.ker := by rw [htop]; exact Subgroup.mem_top x
        have hx1 : (QuotientGroup.mk' (timmesfeldFStar S.Mbar)) (ι x) = 1 := by
          simpa [g, q, MonoidHom.comp_apply] using hmem
        rw [← QuotientGroup.ker_mk' (timmesfeldFStar S.Mbar), MonoidHom.mem_ker]
        exact hx1
      have hcardι : Nat.card ι.range = Nat.card L := by
        rw [show ι.range = (⊤ : Subgroup L).map ι from (Subgroup.map_top ι).symm,
          Subgroup.card_map_of_injective hιinj, Subgroup.card_top]
      have h11F : 11 ∣ Nat.card (timmesfeldFStar S.Mbar) :=
        (hcardι ▸ h11L).trans (Subgroup.card_dvd_of_le hleF)
      rcases hF with h | h
      · obtain ⟨e⟩ := h
        exfalso
        exact h11PSL (by rwa [Nat.card_congr e.toEquiv] at h11F)
      · obtain ⟨e⟩ := h
        haveI : Fintype K := Fintype.ofFinite K
        haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
        have hc : Fintype.card K = Fintype.card (GaloisField 2 2) := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
            GaloisField.card 2 2 (by norm_num)]
          norm_num
        let e' : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K) ≃*
            CFSG.Open.timmesfeldPSU 6 :=
          (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
            (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1)).trans
            (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 6).symm
        have hcardF : Nat.card (timmesfeldFStar S.Mbar) = Nat.card L := by
          rw [Nat.card_congr e.toEquiv, Nat.card_congr φ.toEquiv]
          exact (Nat.card_congr e'.toEquiv).symm
        have heqF : ι.range = timmesfeldFStar S.Mbar :=
          Subgroup.eq_of_le_of_card_ge hleF (hcardF.trans hcardι.symm).le
        intro y hy
        rw [← heqF] at hy
        obtain ⟨l, rfl⟩ := hy
        exact ⟨l, rfl⟩
  · exfalso; obtain ⟨h, -⟩ := h6; omega
  · exfalso; obtain ⟨h, -⟩ := h7; omega
  · exfalso; rcases h8.width_eq with h | h <;> omega

private theorem mem_centralizer_of_inf_eq_bot {G : Type} [Group G] {L Q : Subgroup G} {s : G}
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) (hsQ : s ∈ Q)
    (hQ : ∀ x ∈ L, x * s⁻¹ * x⁻¹ ∈ Q) (hLQ : L ⊓ Q = ⊥) :
    s ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hcL : s * x * s⁻¹ * x⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hsN x).mp hx) (L.inv_mem hx)
  have hcQ : s * x * s⁻¹ * x⁻¹ ∈ Q := by
    have h2 := Q.mul_mem hsQ (hQ x hx)
    simpa [mul_assoc] using h2
  have hc1 : s * x * s⁻¹ * x⁻¹ = 1 := by
    have hc : s * x * s⁻¹ * x⁻¹ ∈ L ⊓ Q := ⟨hcL, hcQ⟩
    rw [hLQ] at hc
    exact Subgroup.mem_bot.mp hc
  calc x * s = (s * x * s⁻¹ * x⁻¹)⁻¹ * (s * x) := by group
    _ = s * x := by rw [hc1, inv_one, one_mul]

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0}

theorem false_of_commute_outer {G : Type} [Group G] [Finite G] [IsSimpleGroup G] [Finite K]
    {b : G} {L : Subgroup G} {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {Bs : Subgroup G} (hG : IsCharTwoType G) (hS : LocalSetting hω b L φ Bs) {W : Subgroup G}
    (hW : W ≤ Subgroup.normalizer (Bs : Set G))
    (hWb : W ⊓ Subgroup.centralizer {b} ≤
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G))
    (hn : ∃ n ∈ W, ∃ hnL : n * b * n⁻¹ ∈ L, φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (hr : ∃ g ∈ W, (∀ y ∈ Bs ⊓ L, g * y * g⁻¹ = y) ∧ g * b * g⁻¹ = b⁻¹ ∧
      ∃ h ∈ Subgroup.normalizer (L : Set G), g * h = h * g ∧ h ^ 3 = 1 ∧
        h ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    (hU12 : ¬ Nonempty (G ≃* timmesfeldPSU 12)) :
    False := by
  obtain ⟨n, hnW, hnL, hnφ⟩ := hn
  obtain ⟨g, hgW, hgB, hgb, h, hhN, hgh, hh3, hhL⟩ := hr
  obtain ⟨t, htg, htN, ht2, htb, htL⟩ := exists_involution hG hS hgB hgb
  have htW : t ∈ W := Subgroup.zpowers_le.mpr hgW htg
  have htnW : n⁻¹ * t * n ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hnW) htW) hnW
  have htCb : n⁻¹ * t * n ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (n * b * n⁻¹) * t = t * (n * b * n⁻¹) :=
      Subgroup.mem_centralizer_iff.mp htL (n * b * n⁻¹) hnL
    calc (n⁻¹ * t * n) * b = n⁻¹ * (t * (n * b * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * b * n⁻¹) * t) * n := by rw [hcomm]
      _ = b * (n⁻¹ * t * n) := by group
  have htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) :=
    hWb (Subgroup.mem_inf.mpr ⟨htnW, htCb⟩)
  have hnA : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ hnL : n * b * n⁻¹ ∈ L,
      φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω ∧ n⁻¹ * t * n ∈
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) :=
    ⟨n, hW hnW, hnL, hnφ, htA⟩
  obtain ⟨S, hz, hQG, hw⟩ := exists_setting_width_ten hG hS htN ht2 htb htL hnA
  have hLM : L ≤ S.M := by
    change L ≤ Subgroup.centralizer ({S.z} : Set G)
    rw [hz]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp htL) x hx)
  have hLQ : L ⊓ S.QG = ⊥ := by
    rw [hQG]
    exact inf_pCoreOf_centralizer_eq_bot hS htL
  obtain ⟨hidx, hsurj⟩ :=
    index_le_two_and_surj_of_setting hS.card_K φ S hw hLM hLQ hT hU12
  have hhM : h ∈ S.M := by
    change h ∈ Subgroup.centralizer ({S.z} : Set G)
    rw [hz, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp htg
    exact (Commute.zpow_left (show Commute g h from hgh) k).symm.eq
  haveI hFnormal : (timmesfeldFStar S.Mbar).Normal := by
    rw [← CFSG.LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar]
    exact (CFSG.LocalCores.generalized_fitting_characteristic).2
  obtain ⟨hb, hbdef⟩ : ∃ y : S.Mbar, y = S.ρ.rangeRestrict ⟨h, hhM⟩ := ⟨_, rfl⟩
  have hb3 : hb ^ 3 = 1 := by
    have hM3 : (⟨h, hhM⟩ : S.M) ^ 3 = 1 := Subtype.ext (by simpa using hh3)
    have h1 : S.ρ.rangeRestrict ((⟨h, hhM⟩ : S.M) ^ 3) = 1 := by rw [hM3, map_one]
    rw [hbdef]
    exact (map_pow S.ρ.rangeRestrict _ 3).symm.trans h1
  have hbF : hb ∈ timmesfeldFStar S.Mbar := by
    let q : S.Mbar →* (S.Mbar ⧸ timmesfeldFStar S.Mbar) := QuotientGroup.mk' _
    have hq3 : orderOf (q hb) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hb3, map_one])
    have hqc : orderOf (q hb) ∣ Nat.card (S.Mbar ⧸ timmesfeldFStar S.Mbar) :=
      orderOf_dvd_natCard _
    have hqcard : Nat.card (S.Mbar ⧸ timmesfeldFStar S.Mbar) ≤ 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have hq1 : orderOf (q hb) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hq3 with h1 | h3
      · exact h1
      · rw [h3] at hqc
        have := Nat.le_of_dvd Nat.card_pos hqc
        omega
    exact (QuotientGroup.eq_one_iff hb).mp (orderOf_eq_one_iff.mp hq1)
  obtain ⟨l, hl⟩ := hsurj hb hbF
  have hsQ : (l : G)⁻¹ * h ∈ S.QG := by
    have hl' : S.ρ ⟨h, hhM⟩ = S.ρ ⟨(l : G), hLM l.2⟩ := by
      rw [hl, hbdef]
      rfl
    have hmem := (MonoidHom.eq_iff S.ρ).mp hl'
    rw [S.ker_ρ] at hmem
    exact ⟨_, hmem, rfl⟩
  have hQGconj : ∀ x ∈ S.M, ∀ y ∈ S.QG, x * y * x⁻¹ ∈ S.QG := by
    intro x hx y hy
    obtain ⟨hyM, hyQ⟩ := S.mem_QG_iff.mp hy
    exact S.mem_QG_iff.mpr ⟨_, S.normal.conj_mem ⟨y, hyM⟩ hyQ ⟨x, hx⟩⟩
  have hsN : (l : G)⁻¹ * h ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer (L.inv_mem l.2)) hhN
  have hsC : (l : G)⁻¹ * h ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_inf_eq_bot hsN hsQ
      (fun x hx => hQGconj x (hLM hx) _ (S.QG.inv_mem hsQ)) hLQ
  apply hhL
  have hhsl : h = (l : G) * ((l : G)⁻¹ * h) := by group
  rw [hhsl]
  exact (L ⊔ Subgroup.centralizer (L : Set G)).mul_mem (Subgroup.mem_sup_left l.2)
    (Subgroup.mem_sup_right hsC)

end LocalSetting

end CFSG.StandardType.USixTwo

end
