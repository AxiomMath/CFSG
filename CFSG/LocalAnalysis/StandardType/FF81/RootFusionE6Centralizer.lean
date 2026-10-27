module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge

public section

namespace CFSG.StandardType.FF81

theorem centralizer_le_of_yData {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {K : ℕ → Subgroup G} {t : G} {Y : Subgroup G} (hA : HypA G n b L)
    (hup : Upstream n b L K t) (hY : YData n b L Y t) (hZ : Subgroup.center ↥Y = ⊥)
    (hcent : Subgroup.centralizer ({t} : Set G) ≤ Y) :
    Subgroup.centralizer ({b} : Set G) ≤ Y := by
  classical
  obtain ⟨z, hz, hF⟩ := hup
  have hb3 : b ^ 3 = 1 := by
    rw [← hA.ord]
    exact pow_orderOf_eq_one b
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hF.ord_t] at h
    simpa [pow_two] using h
  have htY : t ∈ Y := by
    obtain ⟨S, hS, htS, -, -⟩ := hY.syl
    exact hS.1 htS
  have hbY : b ∈ Y := by
    have hb : b ∈ Subgroup.centralizer ({b} : Set G) ⊓ Y := by
      rw [hY.cen_b]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    exact hb.2
  have hbK : b ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have htK : t ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hbL : ∀ y ∈ L, b * y = y * b := fun y hy => hF.comm_L b hbK y hy
  have htL : ∀ y ∈ L, t * y = y * t := fun y hy => hF.comm_L t htK y hy
  let D : Subgroup G :=
    Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
  have hbD : b ∈ D := by
    refine ⟨?_, ?_⟩
    · change b ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => (hbL y hy).symm
    · change b ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      rfl
  have hzD : Subgroup.zpowers b ≤ D := Subgroup.zpowers_le.mpr hbD
  have hP0p : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf D) := by
    have h : IsPGroup 3 (Subgroup.zpowers b) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hA.ord, pow_one]
    exact h.comap_subtype
  have hsyl_max : ∀ Q : Subgroup ↥D, IsPGroup 3 Q →
      (Subgroup.zpowers b).subgroupOf D ≤ Q → Q = (Subgroup.zpowers b).subgroupOf D := by
    intro Q hQ hle
    have hQmap : IsPGroup 3 (Q.map D.subtype) := hQ.map D.subtype
    have hle' : Subgroup.zpowers b ≤ Q.map D.subtype := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hzD hx⟩, hle hx, rfl⟩
    have hEq : Q.map D.subtype = Subgroup.zpowers b :=
      hz.loc.syl (Q.map D.subtype)
        ((Subgroup.map_subtype_le Q).trans inf_le_left)
        ((Subgroup.map_subtype_le Q).trans inf_le_right)
        hQmap hle'
    calc Q = (Q.map D.subtype).comap D.subtype :=
          (Subgroup.comap_map_eq_self (f := D.subtype) (H := Q) (by simp)).symm
      _ = (Subgroup.zpowers b).comap D.subtype := by rw [hEq]
      _ = (Subgroup.zpowers b).subgroupOf D := rfl
  obtain ⟨Q, hQle⟩ := hP0p.exists_le_sylow
  have hQP0 : Q = (Subgroup.zpowers b).subgroupOf D := hsyl_max Q Q.isPGroup' hQle
  have hP0index : ¬ 3 ∣ ((Subgroup.zpowers b).subgroupOf D).index := by
    rw [← hQP0]
    exact Q.not_dvd_index
  let P : Sylow 3 ↥D := hP0p.toSylow hP0index
  have hPcoe : (P : Subgroup ↥D) = (Subgroup.zpowers b).subgroupOf D := rfl
  have hPcenter : (P : Subgroup ↥D) ≤ Subgroup.center ↥D := by
    rw [hPcoe]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : G) ∈ Subgroup.zpowers b := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
    ext
    show (y : G) * (x : G) = (x : G) * (y : G)
    rw [← hk]
    have hyb : Commute (y : G) b :=
      (Subgroup.mem_centralizer_iff.mp y.2.2 b (Set.mem_singleton b)).symm
    exact (hyb.zpow_right k).eq
  obtain ⟨N, hNnormal, hNcomp⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.exists_normal_complement_of_le_center P hPcenter
  have hNindex : N.index = 3 := by
    rw [hNcomp.index_eq_card, hPcoe]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzD).toEquiv, Nat.card_zpowers, hA.ord]
  have h3N : ¬ 3 ∣ Nat.card N := by
    rw [← hNcomp.symm.index_eq_card]
    exact P.not_dvd_index
  let N' : Subgroup G := N.map D.subtype
  have hN'leD : N' ≤ D := Subgroup.map_subtype_le N
  have hcardN' : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective D.subtype_injective
  have h3N' : ¬ 3 ∣ Nat.card N' := by
    rw [hcardN']
    exact h3N
  have hN'_order : ∀ d ∈ D, d ∈ N' ↔ ¬ 3 ∣ orderOf d := by
    intro d hd
    constructor
    · intro hdN
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hdN
      have h1 : orderOf (n : G) ∣ Nat.card N := by
        rw [Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard N hn
      intro h3
      exact h3N (h3.trans h1)
    · intro hd3
      set d' : ↥D := ⟨d, hd⟩ with hd'def
      have hd3' : ¬ 3 ∣ orderOf d' := by
        rw [hd'def, Subgroup.orderOf_mk]
        exact hd3
      have hd3mem : d' ^ 3 ∈ N :=
        letI : N.Normal := hNnormal
        (by
          have hcard : Nat.card (↥D ⧸ N) = 3 := by
            rw [← Subgroup.index_eq_card (H := N), hNindex]
          have hq : (QuotientGroup.mk d' : ↥D ⧸ N) ^ 3 = 1 := by
            have h := pow_card_eq_one' (G := ↥D ⧸ N) (x := QuotientGroup.mk d')
            rwa [hcard] at h
          rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq)
      have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d')) 3 := by
        rw [Nat.card_zpowers]
        exact (Nat.prime_three.coprime_iff_not_dvd.mpr hd3').symm
      obtain ⟨y, hy⟩ :=
        (powCoprime (G := ↥(Subgroup.zpowers d')) (n := 3) hcop).surjective
          ⟨d', Subgroup.mem_zpowers d'⟩
      have hy3 : ((y : ↥D)) ^ 3 = d' := by
        have h1 := congrArg Subtype.val hy
        simpa [powCoprime_apply] using h1
      have hy3z : ((y : ↥D)) ^ (3 : ℤ) = d' := by
        simpa [zpow_natCast] using hy3
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      have hdN : d' ∈ N := by
        have h : d' = (d' ^ (3 : ℤ)) ^ k := by
          have h1 : d' = (d' ^ k) ^ (3 : ℤ) := by
            conv_lhs => rw [← hy3z]
            conv_rhs => rw [hk]
          have h2 : (d' ^ k) ^ (3 : ℤ) = (d' ^ (3 : ℤ)) ^ k := by
            conv_lhs => rw [← zpow_mul]
            conv_rhs => rw [← zpow_mul]
            rw [mul_comm]
          exact h1.trans h2
        rw [h]
        have h3 : d' ^ (3 : ℤ) = d' ^ 3 := zpow_natCast d' 3
        rw [h3]
        exact N.zpow_mem hd3mem k
      exact Subgroup.mem_map.mpr ⟨d', hdN, rfl⟩
  have hN'conj : ∀ g ∈ Subgroup.centralizer ({b} : Set G), ∀ n ∈ N',
      g * n * g⁻¹ ∈ N' := by
    intro g hg n hn
    have hnD : n ∈ D := hN'leD hn
    have hnC : n ∈ Subgroup.centralizer ({b} : Set G) := hnD.2
    have hgC : g * n * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hnC) (Subgroup.inv_mem _ hg)
    have hgL : g * n * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : g⁻¹ * l * g ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hA.nor (Subgroup.inv_mem _ hg)) l).mp hl
      have hnl : (g⁻¹ * l * g) * n = n * (g⁻¹ * l * g) :=
        Subgroup.mem_centralizer_iff.mp hnD.1 (g⁻¹ * l * g) hl'
      calc l * (g * n * g⁻¹) = g * ((g⁻¹ * l * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * l * g)) * g⁻¹ := by rw [hnl]
        _ = (g * n * g⁻¹) * l := by group
    have hgD : g * n * g⁻¹ ∈ D := ⟨hgL, hgC⟩
    have hord : orderOf (g * n * g⁻¹) = orderOf n := by
      have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective n
      simpa [MulAut.conj_apply] using h
    rw [hN'_order (g * n * g⁻¹) hgD, hord]
    exact (hN'_order n hnD).mp hn
  have hN'normalC : (N'.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal :=
    ⟨fun n hn g => by
      change ((g : G) * (n : G) * (g : G)⁻¹) ∈ N'
      exact hN'conj (g : G) g.2 (n : G) hn⟩
  have hN'core : N' ≤ Subgroup.centralizer (Y : Set G) :=
    hY.core N' (hN'leD.trans inf_le_right) hN'normalC h3N'
  have hN'leY : N' ≤ Y := by
    refine hN'core.trans ?_
    refine (Subgroup.centralizer_le ?_).trans hcent
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact htY
  have hN'center : N' ≤ (Subgroup.center ↥Y).map Y.subtype := by
    intro n hn
    refine Subgroup.mem_map.mpr ⟨⟨n, hN'leY hn⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    exact Subgroup.mem_centralizer_iff.mp (hN'core hn) (y : G) y.2
  have hN'bot : N' = ⊥ := by
    have hle : N' ≤ (⊥ : Subgroup G) := by
      simpa [hZ] using hN'center
    exact le_bot_iff.mp hle
  have hNbot : N = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (f := D.subtype) (H := N)
      D.subtype_injective).mp (by simpa [N'] using hN'bot)
  have hPtop : (P : Subgroup ↥D) = ⊤ := by
    have hcomp : (P : Subgroup ↥D).IsComplement' ⊥ := by
      rw [← hNbot]
      exact hNcomp
    exact (Subgroup.isComplement'_bot_right (H := (P : Subgroup ↥D))).mp hcomp
  have hD : D = Subgroup.zpowers b := by
    refine le_antisymm ?_ hzD
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥D) ∈ (P : Subgroup ↥D) := by
      rw [hPtop]
      exact Subgroup.mem_top _
    rw [hPcoe] at hx'
    exact hx'
  intro σ hσ
  set x : G := σ * t * σ⁻¹ with hxdef
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [hxdef, Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : σ⁻¹ * l * σ ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hA.nor (Subgroup.inv_mem _ hσ)) l).mp hl
    have htl : t * (σ⁻¹ * l * σ) = (σ⁻¹ * l * σ) * t := htL _ hl'
    calc l * (σ * t * σ⁻¹) = σ * ((σ⁻¹ * l * σ) * t) * σ⁻¹ := by group
      _ = σ * (t * (σ⁻¹ * l * σ)) * σ⁻¹ := by rw [htl]
      _ = (σ * t * σ⁻¹) * l := by group
  have hσb : σ * b = b * σ :=
    (Subgroup.mem_centralizer_iff.mp hσ b (Set.mem_singleton b)).symm
  have hxinv : x * b * x⁻¹ = b⁻¹ := by
    rw [hxdef]
    have hsb : σ * b * σ⁻¹ = b := by
      calc σ * b * σ⁻¹ = (b * σ) * σ⁻¹ := by rw [hσb]
        _ = b := by group
    calc (σ * t * σ⁻¹) * b * (σ * t * σ⁻¹)⁻¹
        = σ * (t * (σ⁻¹ * b * σ) * t⁻¹) * σ⁻¹ := by group
      _ = σ * (t * b * t⁻¹) * σ⁻¹ := by
            rw [show σ⁻¹ * b * σ = b by
              calc σ⁻¹ * b * σ = σ⁻¹ * (b * σ) := by group
                _ = σ⁻¹ * (σ * b) := by rw [← hσb]
                _ = b := by group]
      _ = σ * b⁻¹ * σ⁻¹ := by rw [hF.inv_b]
      _ = b⁻¹ := by
            calc σ * b⁻¹ * σ⁻¹ = (σ * b * σ⁻¹)⁻¹ := by group
              _ = b⁻¹ := by rw [hsb]
  have htxL : t * x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hxl : l * x = x * l := Subgroup.mem_centralizer_iff.mp hxL l hl
    have htl : t * l = l * t := htL l hl
    calc l * (t * x) = (l * t) * x := by group
      _ = (t * l) * x := by rw [htl]
      _ = t * (l * x) := by group
      _ = t * (x * l) := by rw [hxl]
      _ = (t * x) * l := by group
  have htxC : t * x ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 : (t * x) * b * (t * x)⁻¹ = b := by
      calc (t * x) * b * (t * x)⁻¹ = t * (x * b * x⁻¹) * t⁻¹ := by group
        _ = t * b⁻¹ * t⁻¹ := by rw [hxinv]
        _ = b := by
              calc t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
                _ = (b⁻¹)⁻¹ := by rw [hF.inv_b]
                _ = b := by group
    calc b * (t * x) = ((t * x) * b * (t * x)⁻¹) * (t * x) := by rw [h1]
      _ = (t * x) * b := by group
  have htxD : t * x ∈ D := ⟨htxL, htxC⟩
  have htxP : t * x ∈ Subgroup.zpowers b := by
    rw [← hD]
    exact htxD
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htxP
  have htconj : ∀ m : ℤ, t * b ^ m = b ^ (-m) * t := by
    intro m
    have h1 : MulAut.conj t b = b⁻¹ := by
      simpa [MulAut.conj_apply] using hF.inv_b
    have h2 : MulAut.conj t (b ^ m) = (b⁻¹) ^ m := by
      rw [← h1, map_zpow]
    have h3 : t * b ^ m * t⁻¹ = b ^ (-m) := by
      simpa [MulAut.conj_apply, inv_zpow'] using h2
    calc t * b ^ m = (t * b ^ m * t⁻¹) * t := by group
      _ = b ^ (-m) * t := by rw [h3]
  have hx_eq : x = b ^ (-j) * t := by
    calc x = t * (t * x) := by rw [← mul_assoc, ht2, one_mul]
      _ = t * b ^ j := by rw [← hj]
      _ = (t * b ^ j * t⁻¹) * t := by group
      _ = b ^ (-j) * t := by rw [htconj j]; group
  have hbσC : b ^ (-j) * σ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hconj3 : (b ^ (-j) * σ) * t * (b ^ (-j) * σ)⁻¹ = t := by
      calc (b ^ (-j) * σ) * t * (b ^ (-j) * σ)⁻¹
          = b ^ (-j) * x * b ^ j := by rw [hxdef]; group
        _ = b ^ (-j) * (b ^ (-j) * t) * b ^ j := by rw [hx_eq]
        _ = b ^ (-2 * j) * (t * b ^ j) := by group
        _ = b ^ (-2 * j) * (b ^ (-j) * t) := by rw [htconj j]
        _ = b ^ (-3 * j) * t := by group
        _ = t := by
              have hzero : b ^ (-3 * j) = 1 := by
                have hb3' : b ^ (3 : ℤ) = 1 := by simpa using hb3
                calc b ^ (-3 * j) = b ^ (3 * (-j)) := by congr 1; ring
                  _ = (b ^ (3 : ℤ)) ^ (-j) := zpow_mul b 3 (-j)
                  _ = 1 := by rw [hb3', one_zpow]
              rw [hzero, one_mul]
    calc t * (b ^ (-j) * σ) =
          ((b ^ (-j) * σ) * t * (b ^ (-j) * σ)⁻¹) * (b ^ (-j) * σ) := by
            rw [hconj3]
      _ = (b ^ (-j) * σ) * t := by group
  have hbσY : b ^ (-j) * σ ∈ Y := hcent hbσC
  have hσeq : σ = b ^ j * (b ^ (-j) * σ) := by
    calc σ = (b ^ j * b ^ (-j)) * σ := by
          rw [← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      _ = b ^ j * (b ^ (-j) * σ) := by group
  rw [hσeq]
  exact Y.mul_mem (Y.zpow_mem hbY j) hbσY

end CFSG.StandardType.FF81

end
