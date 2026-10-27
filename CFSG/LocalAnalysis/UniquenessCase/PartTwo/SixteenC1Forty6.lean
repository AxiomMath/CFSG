module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSetupB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Abs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_perfectCore_eq_of_le {B C : Subgroup G} (hCB : C ≤ B) (hle : perfectCore B ≤ C) :
    perfectCore C = perfectCore B :=
  le_antisymm (perfectCore_mono hCB) (le_perfectCore_of_perfect hle (perfectCore_perfect B))

theorem s16c1_starImg_sup_pCoreOf {L Y : Subgroup G} (hYL : Y ≤ L) :
    starImg L (Y ⊔ pCoreOf 2 L) = starImg L Y := by
  have hOle : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hOsub : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    unfold pCoreOf
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hker : (CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  unfold starImg
  rw [Subgroup.subgroupOf_sup hYL hOle, Subgroup.map_sup, hOsub, hker, sup_bot_eq]

private lemma s16c1_factorization_two_pow_mul {k m : ℕ} (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    Nat.factorization (2 ^ k * m) 2 = k := by
  rw [Nat.factorization_def _ Nat.prime_two]
  rw [padicValNat_base_pow_mul (p := 2) (n := m) (by norm_num) hm0]
  rw [padicValNat.eq_zero_of_not_dvd (p := 2) (n := m) hm]
  exact zero_add k

theorem s16c1_isParabolic2In {L Y : Subgroup G} (hYL : Y ≤ L) (hL : Nat.card (Bar2 L) = 25920)
    (hY : Nat.card ↥(starImg L Y) = 960) : IsParabolic2In L (Y ⊔ pCoreOf 2 L) := by
  have hOle : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hPL : Y ⊔ pCoreOf 2 L ≤ L := sup_le hYL hOle
  have hstar : starImg L (Y ⊔ pCoreOf 2 L) = starImg L Y := s16c1_starImg_sup_pCoreOf hYL
  have hcardQ : Nat.card ↥(starImg L (Y ⊔ pCoreOf 2 L)) = 960 := by rw [hstar]; exact hY
  have hstar_top : starImg L L = ⊤ := by
    unfold starImg
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))]
  refine ⟨hPL, ?_, ?_, ?_⟩
  · intro hPeq
    have h1 : Nat.card ↥(starImg L L) = 25920 := by
      rw [hstar_top, Subgroup.card_top, hL]
    rw [hPeq] at hcardQ
    omega
  · change CFSG.pCore 2 ↥L ≤ (Y ⊔ pCoreOf 2 L).comap L.subtype
    exact (Subgroup.map_le_iff_le_comap).mp le_sup_right
  · set Q : Subgroup (Bar2 L) := starImg L (Y ⊔ pCoreOf 2 L) with hQ
    have hQcard : Nat.card ↥Q = 960 := hcardQ
    have hfac960 : Nat.factorization 960 2 = 6 :=
      s16c1_factorization_two_pow_mul (k := 6) (m := 15) (by norm_num) (by norm_num)
    have hfac25920 : Nat.factorization 25920 2 = 6 :=
      s16c1_factorization_two_pow_mul (k := 6) (m := 405) (by norm_num) (by norm_num)
    let S₀ : Sylow 2 ↥Q := Classical.choice (Sylow.nonempty (p := 2) (G := ↥Q))
    have hS₀card : Nat.card ↥(S₀ : Subgroup ↥Q) = 2 ^ 6 := by
      rw [Sylow.card_eq_multiplicity, hQcard, hfac960]
    have hS₁card : Nat.card ↥((S₀ : Subgroup ↥Q).map Q.subtype) = 2 ^ 6 := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective, hS₀card]
    have hS₁pg : IsPGroup 2 ((S₀ : Subgroup ↥Q).map Q.subtype) :=
      IsPGroup.map S₀.isPGroup' Q.subtype
    obtain ⟨S, hSle⟩ := hS₁pg.exists_le_sylow
    have hScard : Nat.card ↥(S : Subgroup (Bar2 L)) = 2 ^ 6 := by
      rw [Sylow.card_eq_multiplicity, hL, hfac25920]
    have hSeq : (S₀ : Subgroup ↥Q).map Q.subtype = S :=
      Subgroup.eq_of_le_of_card_ge hSle (by rw [hScard, hS₁card])
    refine ⟨S, ?_⟩
    change (S : Subgroup (Bar2 L)) ≤ Q
    rw [← hSeq]
    exact Subgroup.map_subtype_le _

private lemma s16c1_pCoreOf_subgroupOf (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  unfold pCoreOf
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

private lemma s16c1_conj_mem_pCoreOf {L : Subgroup G} {l : G} (hl : l ∈ L) :
    ∀ o ∈ pCoreOf 2 L, l * o * l⁻¹ ∈ pCoreOf 2 L := by
  intro o ho
  simp only [pCoreOf, Subgroup.mem_map] at ho ⊢
  obtain ⟨n, hn, rfl⟩ := ho
  exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥L)).conj_mem n hn ⟨l, hl⟩, by simp⟩

private theorem s16c1_mem_sup_pCoreOf_iff {L Y : Subgroup G} (hYL : Y ≤ L) {x : G} :
    x ∈ Y ⊔ pCoreOf 2 L ↔ ∃ y ∈ Y, ∃ o ∈ pCoreOf 2 L, x = y * o := by
  have hOle : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  constructor
  · intro hx
    have hxL : x ∈ L := (sup_le hYL hOle) hx
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ Y.subgroupOf L ⊔ (pCoreOf 2 L).subgroupOf L := by
      rw [← Subgroup.subgroupOf_sup hYL hOle]
      exact hx
    haveI : ((pCoreOf 2 L).subgroupOf L).Normal := by
      rw [s16c1_pCoreOf_subgroupOf]
      infer_instance
    obtain ⟨y, hy, o, ho, hyo⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    exact ⟨(y : G), hy, (o : G), ho, (Subtype.ext_iff.mp hyo).symm⟩
  · rintro ⟨y, hy, o, ho, rfl⟩
    exact (Y ⊔ pCoreOf 2 L).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ho)

theorem s16c1_perfectCore_sup_eq {L Y : Subgroup G} (hYL : Y ≤ L) (hY : ⁅Y, Y⁆ = Y) :
    perfectCore (Y ⊔ pCoreOf 2 L) =
      Y ⊔ pCoreOf 2 (perfectCore (Y ⊔ pCoreOf 2 L)) := by
  have hOle : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hPL : Y ⊔ pCoreOf 2 L ≤ L := sup_le hYL hOle
  have hYX : Y ≤ perfectCore (Y ⊔ pCoreOf 2 L) :=
    le_perfectCore_of_perfect le_sup_left hY
  have hOpg : IsPGroup 2 (pCoreOf 2 L) := by
    unfold pCoreOf
    exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) L.subtype
  have hXO : perfectCore (Y ⊔ pCoreOf 2 L) ⊓ pCoreOf 2 L ≤
      pCoreOf 2 (perfectCore (Y ⊔ pCoreOf 2 L)) := by
    have hNnorm : ((perfectCore (Y ⊔ pCoreOf 2 L) ⊓ pCoreOf 2 L).subgroupOf
        (perfectCore (Y ⊔ pCoreOf 2 L))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left, Subgroup.le_normalizer_iff]
      intro a ha n hn
      exact ⟨(perfectCore _).mul_mem ((perfectCore _).mul_mem ha hn.1)
          ((perfectCore _).inv_mem ha),
        s16c1_conj_mem_pCoreOf ((perfectCore_le _).trans hPL ha) n hn.2⟩
    have hNpg : IsPGroup 2 ((perfectCore (Y ⊔ pCoreOf 2 L) ⊓ pCoreOf 2 L).subgroupOf
        (perfectCore (Y ⊔ pCoreOf 2 L))) :=
      (hOpg.to_le inf_le_right).of_injective
        (Subgroup.subgroupOfEquivOfLe inf_le_left).toMonoidHom
        (by
          rw [MulEquiv.coe_toMonoidHom]
          exact (Subgroup.subgroupOfEquivOfLe inf_le_left).injective)
    have hNle : (perfectCore (Y ⊔ pCoreOf 2 L) ⊓ pCoreOf 2 L).subgroupOf
        (perfectCore (Y ⊔ pCoreOf 2 L)) ≤
        CFSG.pCore 2 ↥(perfectCore (Y ⊔ pCoreOf 2 L)) :=
      le_sSup (s := {K : Subgroup ↥(perfectCore (Y ⊔ pCoreOf 2 L)) |
        K.Normal ∧ IsPGroup 2 K}) ⟨hNnorm, hNpg⟩
    have hmap := Subgroup.map_mono (f := (perfectCore (Y ⊔ pCoreOf 2 L)).subtype) hNle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at hmap
  refine le_antisymm ?_ (sup_le hYX (Subgroup.map_subtype_le _))
  intro x hx
  have hxP : x ∈ Y ⊔ pCoreOf 2 L := perfectCore_le _ hx
  obtain ⟨y, hy, o, ho, hxyo⟩ := (s16c1_mem_sup_pCoreOf_iff hYL).mp hxP
  have hoX : o ∈ perfectCore (Y ⊔ pCoreOf 2 L) := by
    have hone : o = y⁻¹ * x := by rw [hxyo]; group
    rw [hone]
    exact (perfectCore _).mul_mem ((perfectCore _).inv_mem (hYX hy)) hx
  rw [hxyo]
  exact (Y ⊔ pCoreOf 2 (perfectCore (Y ⊔ pCoreOf 2 L))).mul_mem
    (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (hXO ⟨hoX, ho⟩))

theorem s16c1_pCoreOf_ne_bot {V₀ V L Y : Subgroup G} {hV : IsElemAbelian 2 V}
    (hLs : L ≤ stabTil V₀ V) (hYL : Y ≤ L)
    (hker : ∀ g : ↥(stabTil V₀ V), (g : G) ∈ L → actTil V₀ V hV g = 1 → (g : G) ∈ pCoreOf 2 L)
    (hE : IsE16A5 ↥(barSub V₀ V hV Y)) : pCoreOf 2 Y ≠ ⊥ := by
  obtain ⟨N₀, hN₀norm, hN₀rank, -⟩ := hE
  have hN₀card : Nat.card ↥N₀ = 16 := by
    obtain ⟨e⟩ := hN₀rank
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (Fin 4 → ZMod 2) = 16
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hN₀pg : IsPGroup 2 ↥N₀ := IsPGroup.of_card (p := 2) (n := 4) (by rw [hN₀card]; norm_num)
  have hN₀ne : N₀ ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot N₀).mp (by rw [hN₀card]; norm_num)
  let B := barSub V₀ V hV Y
  let φ : ↥Y →* ↥(stabTil V₀ V) := Subgroup.inclusion (le_trans hYL hLs)
  let ψ : ↥Y →* ↥B :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp φ) B (fun y =>
      actTil_mem_barSub V₀ V hV (show (y : G) ∈ Y from y.2) (hLs (hYL y.2)))
  have hψapply : ∀ y : ↥Y, (ψ y : MulAut (Vtil V₀ V hV)) =
      actTil V₀ V hV (φ y) := fun _ => rfl
  have hψsurj : Function.Surjective ψ := by
    intro n
    obtain ⟨g, hgY, hgφ⟩ := (mem_barSub V₀ V hV Y (n : MulAut (Vtil V₀ V hV))).mp n.2
    refine ⟨⟨g.1, hgY⟩, Subtype.ext ?_⟩
    rw [hψapply]
    have hincl : φ (⟨g.1, hgY⟩ : ↥Y) = g := Subtype.ext rfl
    rw [hincl, hgφ]
  let Y₁ : Subgroup ↥Y := N₀.comap ψ
  have hY₁norm : Y₁.Normal := hN₀norm.comap ψ
  have hY₁ne : Y₁ ≠ ⊥ := by
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN₀ne
    obtain ⟨y, hy⟩ := hψsurj n.1
    have hyY₁ : y ∈ Y₁ := by
      show ψ y ∈ N₀
      rw [hy]
      exact n.2
    have hy1 : y ≠ 1 := by
      intro h
      apply hn1
      have h1 : ψ y = 1 := by rw [h, map_one]
      rw [hy] at h1
      exact Subtype.ext h1
    intro hbot
    have : y ∈ (⊥ : Subgroup ↥Y) := hbot ▸ hyY₁
    rw [Subgroup.mem_bot] at this
    exact hy1 this
  have hY₁pg : IsPGroup 2 Y₁ := by
    intro y
    have hyN : ψ y.1 ∈ N₀ := y.2
    obtain ⟨k, hk⟩ := hN₀pg ⟨ψ y.1, hyN⟩
    have hk' : (ψ y.1) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hψpow : ψ (y.1 ^ (2 ^ k)) = 1 := by rw [map_pow, hk']
    have hact : actTil V₀ V hV (φ (y.1 ^ (2 ^ k))) = 1 := by
      have := congrArg Subtype.val hψpow
      simpa [hψapply] using this
    have hmemL : ((φ (y.1 ^ (2 ^ k)) : ↥(stabTil V₀ V)) : G) ∈ L :=
      hYL (y.1 ^ (2 ^ k)).2
    have hpc : ((φ (y.1 ^ (2 ^ k)) : ↥(stabTil V₀ V)) : G) ∈ pCoreOf 2 L :=
      hker _ hmemL hact
    have hpcpg : IsPGroup 2 (pCoreOf 2 L) := by
      unfold pCoreOf
      exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) L.subtype
    obtain ⟨m, hm⟩ := hpcpg ⟨_, hpc⟩
    have hm' : (((φ (y.1 ^ (2 ^ k)) : ↥(stabTil V₀ V)) : G) ^ (2 ^ m)) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hgoalG : ((y.1 : ↥Y) : G) ^ (2 ^ (k + m)) = 1 := by
      have hz : ((φ (y.1 ^ (2 ^ k)) : ↥(stabTil V₀ V)) : G) =
          ((y.1 : ↥Y) : G) ^ (2 ^ k) := by simp [φ]
      rw [hz] at hm'
      rw [show (2 : ℕ) ^ (k + m) = 2 ^ k * 2 ^ m from by rw [pow_add]]
      rw [pow_mul]
      exact hm'
    refine ⟨k + m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ((y.1 : ↥Y) : G) ^ (2 ^ (k + m)) = 1
    exact hgoalG
  have hY₁le : Y₁ ≤ CFSG.pCore 2 ↥Y :=
    le_sSup (s := {K : Subgroup ↥Y | K.Normal ∧ IsPGroup 2 K}) ⟨hY₁norm, hY₁pg⟩
  intro hbot
  apply hY₁ne
  have hpbot : CFSG.pCore 2 ↥Y = ⊥ := by
    have h := hbot
    unfold pCoreOf at h
    rwa [Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥Y) Y.subtype_injective] at h
  exact le_bot_iff.mp (hpbot ▸ hY₁le)

theorem s16c1_fstar_centralizer (D : Data G) {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Fstar (centralizer ({z} : Set G)) = pCoreOf 2 (centralizer ({z} : Set G)) :=
  TwelveEleven.fstar_eq_pCoreOf_of_charTwo
    (D.standing.charTwo _ (uc22p22f_isTwoLocal_centralizer hz1 hz2))

theorem s16c1_odd_relIndex (D : Data G) {H : Subgroup G} (hH : IsSylowIn 2 (D.T ⊓ H) H) :
    Odd (D.M.relIndex H) := by
  have h1 : D.M.relIndex H ∣ (D.T ⊓ H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H ((inf_le_left).trans D.sylowM.le)
  have h2 : ¬ 2 ∣ (D.T ⊓ H).relIndex H := hH.not_dvd_relIndex
  exact Nat.odd_iff.2 (by
    by_contra hc
    exact h2 (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (by omega)) h1))

theorem s16c1_isE16A5_starImg (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) (hU4 : IsU4 (Bar2 L) 1)
    {Y : Subgroup G} (hYL : Y ≤ L) (h : IsE16A5 ↥(barSub V₀ V hV Y)) :
    IsE16A5 ↥(starImg L Y) := by
  let φ : ↥L →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Y' : Subgroup ↥L := Y.subgroupOf L
  have hkerφπ : φ.ker = π.ker := by
    ext l
    have h1 := s16c1_actTil_eq_one_iff D hS hc hU4
      (Subgroup.inclusion (s16c1_le_stabTil D hS) l) l.2
    have h2 : (l : G) ∈ pCoreOf 2 L ↔ l ∈ CFSG.pCore 2 ↥L :=
      Subgroup.mem_map_iff_mem L.subtype_injective
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← h2]
    exact h1
  have hker : (φ.comp Y'.subtype).ker = (π.comp Y'.subtype).ker := by
    rw [← MonoidHom.comap_ker φ Y'.subtype, ← MonoidHom.comap_ker π Y'.subtype, hkerφπ]
  have hYbar : barSub V₀ V hV Y = Y'.map φ := by
    ext φ'
    rw [mem_barSub V₀ V hV Y φ', Subgroup.mem_map]
    constructor
    · rintro ⟨g, hgY, rfl⟩
      refine ⟨⟨(g : G), hYL hgY⟩, hgY, ?_⟩
      show φ ⟨(g : G), hYL hgY⟩ = actTil V₀ V hV g
      exact congrArg (actTil V₀ V hV)
        (Subtype.ext (rfl : ((Subgroup.inclusion (s16c1_le_stabTil D hS))
          ⟨(g : G), hYL hgY⟩ : G) = (g : G)))
    · rintro ⟨y, hy, rfl⟩
      exact actTil_mem_barSub V₀ V hV hy (s16c1_le_stabTil D hS y.2)
  have hYstar : starImg L Y = Y'.map π := rfl
  have hrangeψ : (φ.comp Y'.subtype).range = Y'.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hrangeρ : (π.comp Y'.subtype).range = Y'.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥(barSub V₀ V hV Y) ≃* ↥(starImg L Y) :=
    (MulEquiv.subgroupCongr (hYbar.trans hrangeψ.symm)).trans
      (((QuotientGroup.quotientKerEquivRange (φ.comp Y'.subtype)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivRange (π.comp Y'.subtype)))).trans
        (MulEquiv.subgroupCongr (hrangeρ.trans hYstar.symm)))
  exact s16c1G_isE16A5_congr e h

theorem r16_46_of (D : Data G) (h925 : R925Used D) (h45b : R16_45b D) : R16_46 D := by
  intro V₀ V L hV hS hc hLc hU4 x hx
  obtain ⟨-, hsyl, hE, h3, hq⟩ := h45b V₀ V L hV hS hc x hx
  have hz2 : x.val ^ 2 = 1 := by simpa using hV.2 x.val x.val_mem
  have hYL : xInf L x.val ≤ L := (perfectCore_le _).trans inf_le_right
  have hYperf : ⁅xInf L x.val, xInf L x.val⁆ = xInf L x.val := perfectCore_perfect _
  have hLs := s16c1_le_stabTil D hS
  have hcard1 : Nat.card ↥(starImg L (xInf L x.val)) = 960 := by
    rw [← s16c1_card_barSub_eq_card_starImg D hS hc hU4 hYL]
    exact s16c1_card_of_isE16A5 hE
  have hLcard : Nat.card (Bar2 L) = 25920 := s16c1_card_isU4 hU4
  have hpar := s16c1_isParabolic2In hYL hLcard hcard1
  have hker : ∀ g : ↥(stabTil V₀ V), (g : G) ∈ L → actTil V₀ V hV g = 1 →
      (g : G) ∈ pCoreOf 2 L :=
    fun g hg h1 => (s16c1_actTil_eq_one_iff D hS hc hU4 g hg).1 h1
  have hO2 := s16c1_pCoreOf_ne_bot hLs hYL hker hE
  have hYX : xInf L x.val ≤ perfectCore (xInf L x.val ⊔ pCoreOf 2 L) :=
    le_perfectCore_of_perfect le_sup_left hYperf
  have hYne : xInf L x.val ≠ ⊥ := by
    intro h
    apply hO2
    rw [h]
    exact eq_bot_iff.2 (fun y hy => by
      obtain ⟨k, hk, rfl⟩ := hy
      have : (k : ↥(⊥ : Subgroup G)) = 1 := Subsingleton.elim _ _
      simp [this])
  have hXne : perfectCore (xInf L x.val ⊔ pCoreOf 2 L) ≠ ⊥ :=
    fun h => hYne (eq_bot_iff.2 (h ▸ hYX))
  have hXL : perfectCore (xInf L x.val ⊔ pCoreOf 2 L) ≤ L :=
    (perfectCore_le _).trans (sup_le hYL (by
      rintro _ ⟨k, -, rfl⟩
      exact k.2))
  have hperf_eq : xInf L x.val =
      perfectCore (centralizer ({x.val} : Set G) ⊓ perfectCore (xInf L x.val ⊔ pCoreOf 2 L)) := by
    refine (s16c1_perfectCore_eq_of_le (B := centralizer ({x.val} : Set G) ⊓ L)
      (C := centralizer ({x.val} : Set G) ⊓ perfectCore (xInf L x.val ⊔ pCoreOf 2 L))
      (inf_le_inf_left _ hXL) ?_).symm
    exact le_inf ((perfectCore_le _).trans inf_le_left) hYX
  obtain ⟨hSL, hL3⟩ := h925 L (xInf L x.val ⊔ pCoreOf 2 L)
    (perfectCore (xInf L x.val ⊔ pCoreOf 2 L)) (centralizer ({x.val} : Set G)) (xInf L x.val)
    x.val hLc hU4 hpar rfl hXne hx.not_le (s16c1_fstar_centralizer D hx.ne_one hz2) hperf_eq
    (s16c1_perfectCore_sup_eq hYL hYperf) hO2 (s16c1_odd_relIndex D hsyl) hc.2.2.1 hc.2.2.2
    hx.ne_one hz2 rfl h3 hq hsyl (s16c1_isE16A5_starImg D hS hc hU4 hYL hE)
  exact ⟨h3, hq, hSL, hL3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
