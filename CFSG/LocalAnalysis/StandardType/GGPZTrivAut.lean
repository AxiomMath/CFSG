module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_automizer_le_of_eq_mul {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Y J E D : Subgroup G} (hE : IsElemAbelian p E) (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (hJY : J ≤ Y) (hJq : IsQuasisimple ↥J) (hpJ : p ∣ Nat.card ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hYJ : ∀ u ∈ Y, ∃ j ∈ J, ∃ n ∈ LargeEvenPPrimeCoreOf p Y, u = j * n)
    (hDE : D ≤ E) (hDJ : D ≤ Subgroup.centralizer (J : Set G)) (hED : E = (E ⊓ J) ⊔ D) :
    ggAutomizer Y E ≤ ggAutomizer J E := by
  have hp : p.Prime := Fact.out
  set N : Subgroup G := LargeEvenPPrimeCoreOf p Y with hNdef
  set EJ : Subgroup G := E ⊓ J with hEJdef
  have hNleY : N ≤ Y := by rw [hNdef]; exact Subgroup.map_subtype_le _
  have hNY : Y ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer.trans (ggNormalizer_le_normalizer_pPrimeCoreOf p Y)
  have hEN : E ≤ Subgroup.normalizer (N : Set G) :=
    hEY.trans (ggNormalizer_le_normalizer_pPrimeCoreOf p Y)
  have hcopN : Nat.Coprime p (Nat.card ↥N) := ggPPrimeCoreOf_coprime Y
  have hNinfE : N ⊓ E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxN, hxE⟩ := Subgroup.mem_inf.mp hx
    have h1 : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hE.2 x hxE)
    have h2 : orderOf x ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hxN
    have hco : (orderOf x).Coprime (Nat.card ↥N) :=
      Nat.Coprime.coprime_dvd_left h1 hcopN
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hco h2)
  have hNJcent : N ⊓ J ≤ Subgroup.centralizer (J : Set G) := by
    have hJnorm : J ≤ Subgroup.normalizer ((N ⊓ J : Subgroup G) : Set G) := by
      intro j hj
      exact mem_normalizer_inf (hNY (hJY hj)) (Subgroup.le_normalizer hj)
    have hJq' : CFSG.Assembly.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mpr hJq
    rcases ggLe_center_or_eq_of_normalized hJq' inf_le_right hJnorm with hcent | heq
    · exact hcent
    · exfalso
      have hJleN : J ≤ N := heq ▸ inf_le_left
      have hpN : p ∣ Nat.card ↥N := hpJ.trans (Subgroup.card_dvd_of_le hJleN)
      have hp1 : p = 1 := Nat.Coprime.eq_one_of_dvd hcopN hpN
      exact hp.ne_one hp1
  have hDinfY : D ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    obtain ⟨hdD, hdY⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨j₂, hj₂J, n₂, hn₂N, hd_eq⟩ := hYJ d hdY
    have hdcent : d ∈ Subgroup.centralizer (J : Set G) := hDJ hdD
    have hj₂Z : (⟨j₂, hj₂J⟩ : ↥J) ∈ Subgroup.center ↥J := by
      set Z : Subgroup ↥J := Subgroup.center ↥J with hZdef
      have : Group.IsPerfect ↥J := hJq.1
      have hZbot : Subgroup.center (↥J ⧸ Z) = ⊥ := by
        simpa [Z] using Group.IsPerfect.center_quotient_center_eq_bot ↥J
      have hmk : (QuotientGroup.mk' Z ⟨j₂, hj₂J⟩) ∈ Subgroup.center (↥J ⧸ Z) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective Z q
        rw [← map_mul, ← map_mul]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have hkey : j₂⁻¹ * (t : G) * j₂ = n₂ * (t : G) * n₂⁻¹ := by
          have h := Subgroup.mem_centralizer_iff.mp hdcent (t : G) t.2
          rw [hd_eq] at h
          calc j₂⁻¹ * (t : G) * j₂
              = j₂⁻¹ * ((t : G) * (j₂ * n₂)) * n₂⁻¹ := by group
            _ = j₂⁻¹ * ((j₂ * n₂) * (t : G)) * n₂⁻¹ := by rw [h]
            _ = n₂ * (t : G) * n₂⁻¹ := by group
        set w : G := j₂⁻¹ * (t : G) * j₂ * (t : G)⁻¹ with hwdef
        have hwN : w ∈ N := by
          rw [hwdef]
          have htn : (t : G) * n₂⁻¹ * (t : G)⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hNY (hJY t.2)) n₂⁻¹).mp (N.inv_mem hn₂N)
          have hw' : j₂⁻¹ * (t : G) * j₂ * (t : G)⁻¹
              = n₂ * ((t : G) * n₂⁻¹ * (t : G)⁻¹) := by
            rw [hkey]; group
          rw [hw']
          exact N.mul_mem hn₂N htn
        have hwJ : w ∈ J := by
          rw [hwdef]
          exact J.mul_mem (J.mul_mem (J.mul_mem (J.inv_mem hj₂J) t.2) hj₂J)
            (J.inv_mem t.2)
        have hwcent : w ∈ Subgroup.centralizer (J : Set G) :=
          hNJcent (Subgroup.mem_inf.mpr ⟨hwN, hwJ⟩)
        have hwt : (t : G) * w = w * (t : G) :=
          Subgroup.mem_centralizer_iff.mp hwcent (t : G) t.2
        have hz_eq : j₂⁻¹ * (t : G)⁻¹ * j₂ * (t : G) = w⁻¹ := by
          have h1 : j₂⁻¹ * (t : G) * j₂ = w * (t : G) := by rw [hwdef]; group
          have hwt2 : (t : G)⁻¹ * w⁻¹ * (t : G) = w⁻¹ := by
            have h1' : w⁻¹ * (t : G) = (t : G) * w⁻¹ := by
              calc w⁻¹ * (t : G) = w⁻¹ * ((t : G) * w * w⁻¹) := by group
                _ = w⁻¹ * (w * (t : G) * w⁻¹) := by rw [hwt]
                _ = (t : G) * w⁻¹ := by group
            calc (t : G)⁻¹ * w⁻¹ * (t : G) = (t : G)⁻¹ * (w⁻¹ * (t : G)) := by group
              _ = (t : G)⁻¹ * ((t : G) * w⁻¹) := by rw [h1']
              _ = w⁻¹ := by group
          calc j₂⁻¹ * (t : G)⁻¹ * j₂ * (t : G)
              = (j₂⁻¹ * (t : G) * j₂)⁻¹ * (t : G) := by group
            _ = (w * (t : G))⁻¹ * (t : G) := by rw [h1]
            _ = (t : G)⁻¹ * w⁻¹ * (t : G) := by group
            _ = w⁻¹ := hwt2
        have hzmem : ((t * ⟨j₂, hj₂J⟩)⁻¹ * (⟨j₂, hj₂J⟩ * t) : ↥J).val
            ∈ Subgroup.centralizer (J : Set G) := by
          have hval : ((t * ⟨j₂, hj₂J⟩)⁻¹ * (⟨j₂, hj₂J⟩ * t) : ↥J).val
              = j₂⁻¹ * (t : G)⁻¹ * j₂ * (t : G) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [hval, hz_eq]
          exact (Subgroup.centralizer (J : Set G)).inv_mem hwcent
        exact Subgroup.mem_centralizer_iff.mp hzmem (g : G) g.2
      have hone : QuotientGroup.mk' Z ⟨j₂, hj₂J⟩ = 1 := by
        have hbot : QuotientGroup.mk' Z ⟨j₂, hj₂J⟩ ∈ (⊥ : Subgroup (↥J ⧸ Z)) := by
          rw [← hZbot]; exact hmk
        exact Subgroup.mem_bot.mp hbot
      have : (⟨j₂, hj₂J⟩ : ↥J) ∈ Z :=
        (QuotientGroup.eq_one_iff (x := (⟨j₂, hj₂J⟩ : ↥J))).mp hone
      rwa [hZdef] at this
    have hj₂cent : j₂ ∈ Subgroup.centralizer (J : Set G) := by
      have h := Subgroup.mem_center_iff.mp hj₂Z
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact congrArg Subtype.val (h ⟨t, ht⟩)
    have hdE : d ∈ E := hDE hdD
    have hdn : d ∈ N := by
      have : (N.subgroupOf Y).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNleY).mpr hNY
      let ZJ : Subgroup ↥Y := (Subgroup.center ↥J).map (Subgroup.inclusion hJY)
      let π : ↥Y →* (↥Y ⧸ N.subgroupOf Y) := QuotientGroup.mk' (N.subgroupOf Y)
      have hj₂Y : (⟨j₂, hJY hj₂J⟩ : ↥Y) ∈ ZJ := ⟨⟨j₂, hj₂J⟩, hj₂Z, rfl⟩
      have hn₂ker : (⟨n₂, hNleY hn₂N⟩ : ↥Y) ∈ MonoidHom.ker π := by
        rw [QuotientGroup.ker_mk']
        exact Subgroup.mem_subgroupOf.mpr hn₂N
      have hd_eq' : (⟨d, hdY⟩ : ↥Y) = ⟨j₂, hJY hj₂J⟩ * ⟨n₂, hNleY hn₂N⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact hd_eq
      have hmem : π ⟨d, hdY⟩ ∈ ZJ.map π := by
        have h1 : π ⟨d, hdY⟩ = π ⟨j₂, hJY hj₂J⟩ := by
          rw [hd_eq', map_mul, MonoidHom.mem_ker.mp hn₂ker, mul_one]
        rw [h1]
        exact ⟨⟨j₂, hJY hj₂J⟩, hj₂Y, rfl⟩
      have hcardZJ : Nat.card ↥(ZJ.map π) ∣ Nat.card ↥(Subgroup.center ↥J) := by
        refine (Subgroup.card_map_dvd ZJ π).trans ?_
        rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJY)]
      have hord1 : orderOf (π ⟨d, hdY⟩) ∣ Nat.card ↥(ZJ.map π) :=
        Subgroup.orderOf_dvd_natCard (ZJ.map π) hmem
      have hpow : (π ⟨d, hdY⟩) ^ p = 1 := by
        have h1 : (⟨d, hdY⟩ : ↥Y) ^ p = 1 := by
          apply Subtype.ext
          simpa using hE.2 d hdE
        have h2 := congrArg π h1
        simpa only [map_pow, map_one] using h2
      have hord2 : orderOf (π ⟨d, hdY⟩) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hordZ : orderOf (π ⟨d, hdY⟩) ∣ Nat.card ↥(Subgroup.center ↥J) :=
        hord1.trans hcardZJ
      have horder1 : orderOf (π ⟨d, hdY⟩) = 1 := by
        rcases (Nat.dvd_prime hp).mp hord2 with h | h
        · exact h
        · exact absurd (h ▸ hordZ) hZ
      have hone : π ⟨d, hdY⟩ = 1 := orderOf_eq_one_iff.mp horder1
      have : (⟨d, hdY⟩ : ↥Y) ∈ N.subgroupOf Y := by
        rw [← QuotientGroup.ker_mk' (N.subgroupOf Y)]
        exact MonoidHom.mem_ker.mpr hone
      exact Subgroup.mem_subgroupOf.mp this
    have hd1 : d = 1 := by
      have : d ∈ N ⊓ E := Subgroup.mem_inf.mpr ⟨hdn, hdE⟩
      rw [hNinfE] at this
      exact Subgroup.mem_bot.mp this
    exact hd1
  have decomp : ∀ e ∈ E, ∃ a ∈ EJ, ∃ b ∈ D, e = a * b := by
    intro e he
    have hsupE : (⊤ : Subgroup ↥E) = EJ.subgroupOf E ⊔ D.subgroupOf E := by
      rw [eq_comm, ← Subgroup.subgroupOf_sup inf_le_left hDE, ← hED]
      exact Subgroup.subgroupOf_self E
    have hmem : (⟨e, he⟩ : ↥E) ∈ EJ.subgroupOf E ⊔ D.subgroupOf E := by
      rw [← hsupE]; exact Subgroup.mem_top _
    have : IsMulCommutative ↥E := hE.1
    have : (D.subgroupOf E).Normal := Subgroup.normal_of_comm _
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := EJ.subgroupOf E) (t := D.subgroupOf E)
        (x := (⟨e, he⟩ : ↥E))).mp hmem
    refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G),
      Subgroup.mem_subgroupOf.mp hz, ?_⟩
    simpa using (congrArg Subtype.val hyz).symm
  intro φ hφ
  rw [mem_ggAutomizer_iff] at hφ
  obtain ⟨g, hgY, hgE, hgφ⟩ := hφ
  obtain ⟨j, hjJ, n, hnN, hgn⟩ := hYJ g hgY
  have hd : ∀ a ∈ EJ, j * a * j⁻¹ ∈ EJ := by
    intro a ha
    have haE : a ∈ E := ha.1
    have haJ : a ∈ J := ha.2
    have hgaE : g * a * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE a).mp haE
    have hcN : n * a * n⁻¹ * a⁻¹ ∈ N := by
      have han : a * n * a⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hEN haE) n).mp hnN
      have han' : a * n⁻¹ * a⁻¹ ∈ N := by
        have := N.inv_mem han
        simpa [mul_assoc] using this
      rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
      exact N.mul_mem hnN han'
    have hjcN : j * (n * a * n⁻¹ * a⁻¹) * j⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hNY (hJY hjJ)) _).mp hcN
    set n₁ : G := (j * (n * a * n⁻¹ * a⁻¹) * j⁻¹)⁻¹ with hn₁def
    have hn₁N : n₁ ∈ N := N.inv_mem hjcN
    have hkey : j * a * j⁻¹ = n₁ * (g * a * g⁻¹) := by
      rw [hn₁def, hgn]
      group
    obtain ⟨a', ha'EJ, b, hbD, heq⟩ := decomp (g * a * g⁻¹) hgaE
    have hbY : b ∈ Y := by
      have hb_eq : b = a'⁻¹ * n₁⁻¹ * (j * a * j⁻¹) := by
        have he1 : g * a * g⁻¹ = n₁⁻¹ * (j * a * j⁻¹) := by
          calc g * a * g⁻¹ = n₁⁻¹ * (n₁ * (g * a * g⁻¹)) := by group
            _ = n₁⁻¹ * (j * a * j⁻¹) := by rw [← hkey]
        rw [show b = a'⁻¹ * (g * a * g⁻¹) by rw [heq]; group, he1]
        group
      rw [hb_eq]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hJY ha'EJ.2))
        (Y.inv_mem (hNleY hn₁N))) (hJY (J.mul_mem (J.mul_mem hjJ haJ) (J.inv_mem hjJ)))
    have hb1 : b = 1 := by
      have : b ∈ D ⊓ Y := Subgroup.mem_inf.mpr ⟨hbD, hbY⟩
      rw [hDinfY] at this
      exact Subgroup.mem_bot.mp this
    have he_eq : g * a * g⁻¹ = a' := by rw [heq, hb1, mul_one]
    have hn₁_eq : n₁ = (j * a * j⁻¹) * a'⁻¹ := by
      rw [hkey, he_eq]; group
    have hn₁J : n₁ ∈ J := by
      rw [hn₁_eq]
      exact J.mul_mem (J.mul_mem (J.mul_mem hjJ haJ) (J.inv_mem hjJ)) (J.inv_mem ha'EJ.2)
    have hn₁cent : n₁ ∈ Subgroup.centralizer (J : Set G) :=
      hNJcent (Subgroup.mem_inf.mpr ⟨hn₁N, hn₁J⟩)
    have hcomm : a' * n₁ = n₁ * a' :=
      Subgroup.mem_centralizer_iff.mp hn₁cent a' ha'EJ.2
    have hn₁pow : n₁ ^ p = 1 := by
      have hy_pow : a' ^ p = 1 := hE.2 a' ha'EJ.1
      have hjapow : (j * a * j⁻¹) ^ p = 1 := by
        rw [show j * a * j⁻¹ = (MulAut.conj j) a by rw [MulAut.conj_apply], ← map_pow,
          hE.2 a haE, map_one]
      have h1 : (n₁ * a') ^ p = 1 := by
        rw [show n₁ * a' = j * a * j⁻¹ by rw [hkey, he_eq]]
        exact hjapow
      rw [Commute.mul_pow hcomm.symm, hy_pow, mul_one] at h1
      exact h1
    have hn₁1 : n₁ = 1 := by
      have hdvd : orderOf n₁ ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hn₁N
      have hdvd' : orderOf n₁ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hn₁pow
      have hco : (orderOf n₁).Coprime (Nat.card ↥N) :=
        Nat.Coprime.coprime_dvd_left hdvd' hcopN
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hco hdvd)
    have hfinal : j * a * j⁻¹ = a' := by
      rw [hkey, he_eq, hn₁1, one_mul]
    rw [hfinal]
    exact ha'EJ
  have hconj_mem : ∀ x ∈ E, j * x * j⁻¹ ∈ E := by
    intro x hx
    obtain ⟨a', ha'EJ, b, hbD, hx_eq⟩ := decomp x hx
    have hb_cent : j * b * j⁻¹ = b := by
      have h := Subgroup.mem_centralizer_iff.mp (hDJ hbD) j hjJ
      calc j * b * j⁻¹ = (b * j) * j⁻¹ := by rw [h]
        _ = b := by group
    have hmb : (j * a' * j⁻¹) * b ∈ E := by
      rw [hED]
      exact Subgroup.mul_mem_sup (hd a' ha'EJ) hbD
    have hx' : j * x * j⁻¹ = (j * a' * j⁻¹) * b := by
      rw [hx_eq]
      calc j * (a' * b) * j⁻¹ = (j * a' * j⁻¹) * (j * b * j⁻¹) := by group
        _ = (j * a' * j⁻¹) * b := by rw [hb_cent]
    rw [hx']
    exact hmb
  have hjE : j ∈ Subgroup.normalizer (E : Set G) := by
    have hmap : E.map (MulAut.conj j).toMonoidHom ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      rw [show (MulEquiv.toMonoidHom (MulAut.conj j)) x = (MulAut.conj j) x from rfl,
        MulAut.conj_apply]
      exact hconj_mem x hx
    exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hmap
      (Subgroup.card_map_of_injective (MulAut.conj j).injective).ge)
  have hn_cent : ∀ x ∈ E, n * x * n⁻¹ = x := by
    intro x hx
    have hnE : n ∈ Subgroup.normalizer (E : Set G) := by
      rw [show n = j⁻¹ * g by rw [hgn]; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hjE) hgE
    have h1 : n * x * n⁻¹ * x⁻¹ ∈ E :=
      E.mul_mem ((Subgroup.mem_normalizer_iff.mp hnE x).mp hx) (E.inv_mem hx)
    have h2 : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have hxn : x * n⁻¹ * x⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hEN hx) n⁻¹).mp (N.inv_mem hnN)
      rw [show n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) by group]
      exact N.mul_mem hnN hxn
    have h3 : n * x * n⁻¹ * x⁻¹ = 1 := by
      have : n * x * n⁻¹ * x⁻¹ ∈ N ⊓ E := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hNinfE] at this
      exact Subgroup.mem_bot.mp this
    calc n * x * n⁻¹ = (n * x * n⁻¹ * x⁻¹) * x := by group
      _ = x := by rw [h3, one_mul]
  have hconj_eq : ∀ x ∈ E, g * x * g⁻¹ = j * x * j⁻¹ := by
    intro x hx
    rw [hgn]
    calc j * n * x * (j * n)⁻¹ = j * (n * x * n⁻¹) * j⁻¹ := by group
      _ = j * x * j⁻¹ := by rw [hn_cent x hx]
  rw [mem_ggAutomizer_iff]
  refine ⟨j, hjJ, hjE, ?_⟩
  intro b
  rw [hgφ b]
  exact hconj_eq b b.2

end CFSG.StandardType

end
