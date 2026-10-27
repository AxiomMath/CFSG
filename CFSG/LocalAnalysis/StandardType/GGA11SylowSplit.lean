module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecHolds
public import CFSG.LocalAnalysis.StandardType.GGL45NtLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordLift
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open Matrix Pointwise
open CFSG.EvenSmallLie.CatalogOrders

namespace CFSG.StandardType.A11

private theorem a11ss_largeEvenInduces_iff {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (a : MulAut K) (φ : MulAut R) :
    LargeEvenInduces θ (fun l l' : K => l' = a l) φ ↔ φ = ggInducedAut θ a := by
  constructor
  · intro h
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [h l (a l) rfl, ggInducedAut_apply]
  · intro h l l' hl
    rw [h, hl, ggInducedAut_apply]

private theorem a11ss_inducedAut_normalizerMonoidHom {G : Type} [Group G] {K' : Subgroup G}
    {R : Type} [Group R] (θ : ↥K' ⧸ Subgroup.center ↥K' ≃* R) (g : ↥K') :
    ggInducedAut θ (K'.normalizerMonoidHom ⟨(g : G), K'.le_normalizer g.2⟩) =
      MulAut.conj (θ (g : ↥K' ⧸ Subgroup.center ↥K')) := by
  ext r
  obtain ⟨z, rfl⟩ := θ.surjective r
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [ggInducedAut_apply, MulAut.conj_apply]
  change θ (↑g * ↑x * ↑g⁻¹) = θ ↑g * θ ↑x * (θ ↑g)⁻¹
  simp

private theorem a11ss_main {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y' : G} {K' : Subgroup G}
    (hcfg : GGConfig 7 B Bs x L D J) (hnb : GGNbr 7 B x D J y' K')
    (hBsN : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K')
    (hcardBs : Nat.card Bs = 7 ^ 4)
    {R : Type} [Group R] (I F : Set (MulAut R))
    (θ : ↥K' ⧸ Subgroup.center ↥K' ≃* R)
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hrec : GGL45NtRec 7 R I F)
    (hφ : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥K' => ((l' : G) = (b : G)⁻¹ * (l : G) * (b : G))) φ)
    (hperf : commutator ↥K' = ⊤) (hRord : ¬ 7 ^ 4 ∣ Nat.card R) :
    ∃ E : Subgroup G, E ≤ K' ∧ E ≤ Bs ∧ commutator ↥K' = ⊤ ∧ Nat.card E = 7 ^ 3 ∧
      ¬ 7 ^ 4 ∣ Nat.card K' ∧ Bs = Subgroup.zpowers y' ⊔ E ∧ y' ∉ E := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hyB : y' ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hy7 : y' ^ 7 = 1 := hnb.1.1.1.2 y' hnb.1.2.1
  have hyne : y' ≠ 1 := hnb.1.2.2.1
  have hBsab : IsElemAbelian 7 Bs := hcfg.2.1.2.1
  have hpow : ∀ b : ↥Bs, (b : G) ^ 7 = 1 := fun b => hBsab.2 b b.2
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  let Z : Subgroup ↥K' := Subgroup.center ↥K'
  let π : ↥K' →* ↥K' ⧸ Z := QuotientGroup.mk' Z
  let φ : ↥K' →* R := θ.toMonoidHom.comp π
  have hφsurj : Function.Surjective φ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hkerφ : φ.ker = Z := by
    ext z
    rw [MonoidHom.mem_ker]
    constructor
    · intro hz
      have : π z = 1 := θ.injective (by simpa [φ] using hz)
      simpa [Z, π] using this
    · intro hz
      simp [φ, π, hz]
  obtain ⟨hInnR, hInnerP, hCP⟩ := hrec hs hna
  have hZ : ¬ 7 ∣ Nat.card Z := by
    have := hCP ↥K' φ hφsurj (by rw [hkerφ]) hperf
    simpa [Z] using this
  have hCK : Bs ⊓ Subgroup.centralizer (K' : Set G) = Subgroup.zpowers y' :=
    GGNbr.bstar_inf_centralizer_eq_zpowers hcfg hnb hCJ hJK
  have hcardCK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) = 7 := by
    rw [hCK, Nat.card_zpowers, orderOf_eq_prime hy7 hyne]
  have hI : ∀ x : ↥Bs, ggInducedAut θ (K'.normalizerMonoidHom
      ⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩) ∈ I := by
    intro x
    obtain ⟨ψ, hψI, hψ⟩ := hφ x x.2
    have hx : (fun l l' : ↥K' => (l' : G) = (x : G)⁻¹ * (l : G) * (x : G)) =
        (fun l l' : ↥K' => l' = K'.normalizerMonoidHom
          ⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩ l) := by
      funext l l'
      apply propext
      constructor
      · intro h
        exact Subtype.ext (by rw [normalizerMonoidHom_apply_coe]; simpa using h)
      · intro h
        have := congrArg Subtype.val h
        rw [normalizerMonoidHom_apply_coe] at this
        simpa using this
    rw [hx] at hψ
    rw [a11ss_largeEvenInduces_iff] at hψ
    exact hψ ▸ hψI
  have hPE : ∀ x : ↥Bs, GGL45IsPElt 7
      (ggInducedAut θ (K'.normalizerMonoidHom ⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩)) := by
    intro x
    have hnm : (K'.normalizerMonoidHom
        ⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩ : MulAut ↥K') ^ 7 = 1 := by
      rw [← map_pow]
      have harg : (⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩ :
          Subgroup.normalizer (K' : Set G)) ^ 7 = ⟨((x : G)⁻¹) ^ 7, _⟩ := rfl
      rw [harg, normalizerMonoidHom_eq_one_iff]
      have hx7 : ((x : G)⁻¹) ^ 7 = 1 := by rw [inv_pow, hpow x, inv_one]
      rw [hx7]
      exact Subgroup.one_mem _
    refine ⟨1, ?_⟩
    show (ggInducedAut θ (K'.normalizerMonoidHom
      ⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩)) ^ 7 = 1
    rw [← map_pow, hnm, map_one]
  let κ₀ : ↥Bs → R := fun x => Classical.choose (hInnerP _ (hI x) (hPE x))
  have hκ₀ : ∀ x : ↥Bs,
      ggInducedAut θ (K'.normalizerMonoidHom ⟨(x : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩) =
        MulAut.conj (κ₀ x) :=
    fun x => Classical.choose_spec (hInnerP _ (hI x) (hPE x))
  have hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    mulAut_conj_injective (center_eq_bot_of_simple_nonabelian hna)
  have hxy_aux : ∀ x y : ↥Bs,
      K'.normalizerMonoidHom ⟨((x * y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ (x*y).2)⟩ =
        K'.normalizerMonoidHom ⟨((y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ y.2)⟩ *
          K'.normalizerMonoidHom ⟨((x : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩ := by
    intro x y
    have h1 : (⟨((x * y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ (x*y).2)⟩ :
        Subgroup.normalizer (K' : Set G)) =
        ⟨((y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ y.2)⟩ *
          ⟨((x : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      rw [_root_.mul_inv_rev]
    rw [h1, map_mul]
  have hκ₀_anti : ∀ x y : ↥Bs, κ₀ (x * y) = κ₀ y * κ₀ x := by
    intro x y
    apply hconj_inj
    calc MulAut.conj (κ₀ (x * y))
        = ggInducedAut θ (K'.normalizerMonoidHom
            ⟨((x * y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ (x*y).2)⟩) :=
          (hκ₀ (x * y)).symm
      _ = ggInducedAut θ (K'.normalizerMonoidHom
            ⟨((y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ y.2)⟩ *
          K'.normalizerMonoidHom ⟨((x : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩) := by
          rw [hxy_aux x y]
      _ = ggInducedAut θ (K'.normalizerMonoidHom
            ⟨((y : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ y.2)⟩) *
          ggInducedAut θ (K'.normalizerMonoidHom
            ⟨((x : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ x.2)⟩) := map_mul _ _ _
      _ = MulAut.conj (κ₀ y) * MulAut.conj (κ₀ x) := by rw [hκ₀ y, hκ₀ x]
      _ = MulAut.conj (κ₀ y * κ₀ x) := (map_mul _ _ _).symm
  have hκ₀_one : κ₀ 1 = 1 := by
    apply hconj_inj
    rw [map_one, ← hκ₀ 1]
    have harg : (⟨((1 : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ (1 : ↥Bs).2)⟩ :
        Subgroup.normalizer (K' : Set G)) = 1 := Subtype.ext (by simp)
    rw [harg, map_one]
    exact map_one (ggInducedAut θ)
  let f : ↥Bs →* R :=
    { toFun := fun b => κ₀ b⁻¹
      map_one' := by rw [show (1 : ↥Bs)⁻¹ = 1 from inv_one, hκ₀_one]
      map_mul' := by
        intro a b
        rw [show (a * b)⁻¹ = b⁻¹ * a⁻¹ from _root_.mul_inv_rev a b]
        exact hκ₀_anti (b⁻¹) (a⁻¹) }
  have hf_conj : ∀ b : ↥Bs,
      MulAut.conj (f b) = ggInducedAut θ (K'.normalizerMonoidHom
        ⟨(b : G), hBsN b.2⟩) := by
    intro b
    have h2 : K'.normalizerMonoidHom
        ⟨((b⁻¹ : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ (b⁻¹).2)⟩ =
        K'.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩ := by
      congr 1
      exact Subtype.ext (by simp)
    calc MulAut.conj (f b) = MulAut.conj (κ₀ b⁻¹) := by rw [show f b = κ₀ b⁻¹ from rfl]
      _ = ggInducedAut θ (K'.normalizerMonoidHom
            ⟨((b⁻¹ : ↥Bs) : G)⁻¹, hBsN (Subgroup.inv_mem _ (b⁻¹).2)⟩) := (hκ₀ b⁻¹).symm
      _ = ggInducedAut θ (K'.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩) := by rw [h2]
  have hkerf : f.ker = (Bs ⊓ Subgroup.centralizer (K' : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hb
      refine ⟨b.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : ggInducedAut θ (K'.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩) = 1 := by
        rw [← hf_conj b, hb, map_one]
      have h2 : K'.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩ = 1 :=
        ggInducedAut_injective_of_perfect hperf θ (by simpa using h1)
      have h3 : (b : G) ∈ Subgroup.centralizer (K' : Set G) :=
        (normalizerMonoidHom_eq_one_iff (X := K') (hBsN b.2)).mp h2
      exact Subgroup.mem_centralizer_iff.mp h3 k hk
    · rintro ⟨hbBs, hbK⟩
      apply hconj_inj
      have h2 : K'.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩ = 1 :=
        (normalizerMonoidHom_eq_one_iff (X := K') (hBsN b.2)).mpr hbK
      have h1 : ggInducedAut θ (K'.normalizerMonoidHom ⟨(b : G), hBsN b.2⟩) = 1 := by
        rw [h2, map_one]
      rw [← hf_conj b] at h1
      simpa using h1
  have hcardkerf : Nat.card f.ker = 7 := by
    rw [hkerf]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcardCK
  let Ē : Subgroup R := f.range
  have hcardEbar : Nat.card Ē = 7 ^ 3 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hcardkerf, hcardBs] at h
    have h74 : (7 : ℕ) ^ 4 = 7 ^ 3 * 7 := by norm_num
    rw [h74, mul_comm 7 (Nat.card f.range)] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 7) h
  have hEbar_ab : IsElemAbelian 7 Ē := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
      congr 1
      exact (isMulCommutative_iff.mp hBsab.1) x y
    · intro a ha
      obtain ⟨x, rfl⟩ := ha
      rw [← map_pow]
      have hx7 : x ^ 7 = 1 := Subtype.ext (hpow x)
      rw [hx7, map_one]
  let P : Subgroup ↥K' := Ē.comap φ
  have hZleP : Z ≤ P := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : φ z = 1 := by
      have : z ∈ φ.ker := by rw [hkerφ]; exact hz
      exact MonoidHom.mem_ker.mp this
    rw [hz1]
    exact Ē.one_mem
  let ZP : Subgroup P := Z.subgroupOf P
  have hZPcard : Nat.card ZP = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleP).toEquiv
  have hrangeP : (φ.comp P.subtype).range = Ē := by
    apply le_antisymm
    · rintro r ⟨z, rfl⟩
      exact z.2
    · intro r hr
      obtain ⟨z, hz⟩ := hφsurj r
      exact ⟨⟨z, by rw [Subgroup.mem_comap, hz]; exact hr⟩, hz⟩
  have hkerP : (φ.comp P.subtype).ker = ZP := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hkerφ]
    rfl
  haveI hZPnormal : ZP.Normal := hkerP ▸ MonoidHom.normal_ker (φ.comp P.subtype)
  have hPcard : Nat.card P = Nat.card Z * 7 ^ 3 := by
    have h := Subgroup.card_ker_mul_card_range (φ.comp P.subtype)
    rw [hkerP, hrangeP, hcardEbar, hZPcard] at h
    exact h.symm
  have hindex : ZP.index = 7 ^ 3 := by
    have h := Subgroup.card_mul_index ZP
    rw [hZPcard, hPcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hcop : Nat.Coprime (Nat.card ZP) ZP.index := by
    rw [hZPcard, hindex]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr hZ).symm.pow_right 3
  obtain ⟨S, hScomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := ZP) hcop
  let E₀ : Subgroup ↥K' := S.map P.subtype
  have hE₀card : Nat.card E₀ = 7 ^ 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    have h := hScomp.card_mul_card
    rw [hZPcard, hPcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hφE : (φ.comp E₀.subtype).range = Ē := by
    apply le_antisymm
    · rintro r ⟨x, rfl⟩
      obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp x.2
      have hmem : (φ.comp P.subtype) s ∈ (φ.comp P.subtype).range := ⟨s, rfl⟩
      rw [hrangeP] at hmem
      have hxs : (φ.comp E₀.subtype) x = (φ.comp P.subtype) s := by
        change φ (↑x : ↥K') = φ (P.subtype s)
        rw [← hsx]
      rwa [hxs]
    · intro r hr
      have hrP : r ∈ (φ.comp P.subtype).range := by rw [hrangeP]; exact hr
      obtain ⟨p, hp⟩ := hrP
      have hp' : p ∈ ZP ⊔ S := hScomp.sup_eq_top ▸ Subgroup.mem_top p
      obtain ⟨z, hz, s, hs, hzs⟩ := (Subgroup.mem_sup_of_normal_left.mp hp')
      refine ⟨⟨s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩, ?_⟩
      have hs_eq : (φ.comp E₀.subtype) ⟨s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩ =
          (φ.comp P.subtype) s := rfl
      rw [hs_eq, ← hp, ← hzs, map_mul]
      have hz1 : (φ.comp P.subtype) z = 1 := by
        have : z ∈ (φ.comp P.subtype).ker := by rw [hkerP]; exact hz
        exact MonoidHom.mem_ker.mp this
      rw [hz1, one_mul]
  have hφE_inj : Function.Injective (φ.comp E₀.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp x.2
    have hxP : s ∈ ZP ⊓ S := by
      refine ⟨?_, hs⟩
      have hker : s ∈ (φ.comp P.subtype).ker := by
        rw [MonoidHom.mem_ker]
        show (φ.comp P.subtype) s = 1
        rw [show (φ.comp P.subtype) s = (φ.comp E₀.subtype) x from by
          change φ (P.subtype s) = φ (↑x : ↥K')
          rw [← hsx]]
        exact hx
      rwa [hkerP] at hker
    have hxbot : s ∈ (⊥ : Subgroup P) := by
      rw [← hScomp.disjoint.eq_bot]
      exact hxP
    have hs1 : s = 1 := Subgroup.mem_bot.mp hxbot
    exact Subtype.ext (by rw [← hsx, hs1]; rfl)
  have hE₀ab : IsElemAbelian 7 E₀ := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      refine hφE_inj ?_
      rw [map_mul, map_mul]
      have ha' : (φ.comp E₀.subtype) a ∈ Ē := by rw [← hφE]; exact ⟨a, rfl⟩
      have hb' : (φ.comp E₀.subtype) b ∈ Ē := by rw [← hφE]; exact ⟨b, rfl⟩
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hEbar_ab.1) ⟨_, ha'⟩ ⟨_, hb'⟩)
    · intro a ha
      have ha' : φ a ∈ Ē := by rw [← hφE]; exact ⟨⟨a, ha⟩, rfl⟩
      have h1 : ((⟨a, ha⟩ : E₀) ^ 7 : E₀) = 1 := by
        refine hφE_inj ?_
        rw [map_pow, map_one]
        exact hEbar_ab.2 _ ha'
      exact Subtype.ext (congrArg (fun x : E₀ => ((x : ↥K') : G)) h1)
  let φE : E₀ →* Ē := (φ.comp E₀.subtype).codRestrict Ē fun x => by
    rw [← hφE]; exact ⟨x, rfl⟩
  have hφE_bij : Function.Bijective φE := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hφE_inj
      exact congrArg Subtype.val hxy
    · intro y
      have hy : (y : R) ∈ (φ.comp E₀.subtype).range := by rw [hφE]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  let φE_equiv : E₀ ≃* Ē := MulEquiv.ofBijective φE hφE_bij
  let fE : ↥Bs →* Ē := f.codRestrict Ē fun b => ⟨b, rfl⟩
  have hfE_surj : Function.Surjective fE := by
    intro y
    obtain ⟨b, hb⟩ := y.2
    exact ⟨b, Subtype.ext hb⟩
  let κ : ↥Bs →* E₀ := φE_equiv.symm.toMonoidHom.comp fE
  have hκ_surj : Function.Surjective κ := φE_equiv.symm.surjective.comp hfE_surj
  have hφκ : ∀ b : ↥Bs, φ ((κ b : E₀) : ↥K') = f b := by
    intro b
    have h1 : φE (κ b) = fE b := by
      change φE_equiv (φE_equiv.symm (fE b)) = fE b
      rw [MulEquiv.apply_symm_apply]
    have h2 : ((φE (κ b) : Ē) : R) = (fE b : R) := congrArg Subtype.val h1
    exact h2
  have hconjκ : ∀ β : ↥Bs,
      K'.normalizerMonoidHom ⟨(((κ β : E₀) : ↥K') : G), K'.le_normalizer (((κ β : E₀) : ↥K')).2⟩ =
        K'.normalizerMonoidHom ⟨(β : G), hBsN β.2⟩ := by
    intro β
    apply ggInducedAut_injective_of_perfect hperf θ
    rw [a11ss_inducedAut_normalizerMonoidHom]
    have hθ : θ (((κ β : E₀) : ↥K') : ↥K' ⧸ Subgroup.center ↥K') = f β := by
      have := hφκ β
      simp only [φ, MonoidHom.comp_apply] at this
      exact this
    rw [hθ, hf_conj β]
  let E : Subgroup G := E₀.map K'.subtype
  have hE_le_K' : E ≤ K' := by
    rintro z ⟨y, hy, rfl⟩
    exact y.2
  have hEcard : Nat.card E = 7 ^ 3 := by
    rw [Subgroup.card_map_of_injective K'.subtype_injective]
    exact hE₀card
  have hE_le_Bs : E ≤ Bs := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := hκ_surj ⟨y, hy⟩
    have hy_eq : (y : G) = (((κ b : E₀) : ↥K') : G) :=
      congrArg (fun x : E₀ => ((x : ↥K') : G)) hb.symm
    change (y : G) ∈ Bs
    rw [hy_eq]
    apply hSC
    · rw [Subgroup.mem_centralizer_iff]
      intro β hβ
      have hc := congrArg (fun (a : MulAut ↥K') => (((a ((κ b : E₀) : ↥K')) : ↥K') : G))
        (hconjκ ⟨β, hβ⟩)
      simp only [normalizerMonoidHom_apply_coe] at hc
      have hcomm : (((κ ⟨β, hβ⟩ : E₀) : ↥K') : G) * (((κ b : E₀) : ↥K') : G) =
          (((κ b : E₀) : ↥K') : G) * (((κ ⟨β, hβ⟩ : E₀) : ↥K') : G) :=
        congrArg (fun x : E₀ => ((x : ↥K') : G))
          ((isMulCommutative_iff.mp hE₀ab.1) (κ ⟨β, hβ⟩) (κ b))
      have h2 : (((κ ⟨β, hβ⟩ : E₀) : ↥K') : G) * (((κ b : E₀) : ↥K') : G) *
          ((((κ ⟨β, hβ⟩ : E₀) : ↥K') : G))⁻¹ = (((κ b : E₀) : ↥K') : G) := by
        rw [hcomm]; group
      have hconj : β * (((κ b : E₀) : ↥K') : G) * β⁻¹ = (((κ b : E₀) : ↥K') : G) := by
        rw [← hc, h2]
      calc β * (((κ b : E₀) : ↥K') : G)
          = (β * (((κ b : E₀) : ↥K') : G) * β⁻¹) * β := by group
        _ = (((κ b : E₀) : ↥K') : G) * β := by rw [hconj]
    · exact congrArg (fun x : ↥K' => (x : G))
        (hE₀ab.2 ((κ b : E₀) : ↥K') (κ b : E₀).2)
  refine ⟨E, hE_le_K', hE_le_Bs, hperf, ?_, ?_, ?_, ?_⟩
  · exact hEcard
  ·
    have hK'card : Nat.card ↥K' = Nat.card Z * Nat.card R := by
      have h := Subgroup.card_mul_index Z
      rw [← h]
      congr 1
      exact Nat.card_congr θ.toEquiv
    rintro hdvd
    rw [hK'card] at hdvd
    have hcop74 : Nat.Coprime (7 ^ 4) (Nat.card Z) := by
      rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 4)]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr hZ
    exact hRord (hcop74.dvd_of_dvd_mul_left hdvd)
  ·
    have hy'E : E ⊓ Subgroup.zpowers y' = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzE, hzy⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hzE
      obtain ⟨b, hb⟩ := hκ_surj ⟨y, hy⟩
      have hy_eq : (y : G) = (((κ b : E₀) : ↥K') : G) :=
        congrArg (fun x : E₀ => ((x : ↥K') : G)) hb.symm
      rw [Subgroup.mem_bot]
      change (y : G) = 1
      have hmem : (((κ b : E₀) : ↥K') : G) ∈ Subgroup.zpowers y' := by
        rw [← hy_eq]; exact hzy
      have hzC : (((κ b : E₀) : ↥K') : G) ∈ Subgroup.centralizer (K' : Set G) := by
        rw [← hCK] at hmem
        exact hmem.2
      have hzZ : ((κ b : E₀) : ↥K') ∈ Z := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hzC (g : G) g.2
      have hz7 : (((κ b : E₀) : ↥K') : G) ^ 7 = 1 := by
        have h := hE₀ab.2 ((κ b : E₀) : ↥K') (κ b : E₀).2
        exact congrArg (fun x : ↥K' => (x : G)) h
      by_cases hz1 : (((κ b : E₀) : ↥K') : G) = 1
      · exact hy_eq.trans hz1
      · exfalso
        have hord : orderOf (((κ b : E₀) : ↥K') : G) = 7 :=
          orderOf_eq_prime hz7 hz1
        have hdvd : 7 ∣ Nat.card Z := by
          rw [← hord, Subgroup.orderOf_coe (((κ b : E₀) : ↥K')),
            Subgroup.orderOf_coe (⟨((κ b : E₀) : ↥K'), hzZ⟩ : Z)]
          exact orderOf_dvd_natCard _
        exact hZ hdvd
    have hnorm : Subgroup.zpowers y' ≤ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        have heBs : e ∈ Bs := hE_le_Bs he
        have h2 : y' * e = e * y' :=
          congrArg (fun x : ↥Bs => (x : G))
            ((isMulCommutative_iff.mp hBsab.1) ⟨y', hyB⟩ ⟨e, heBs⟩)
        have hcomm : y' * e * y'⁻¹ = e := by rw [h2]; group
        rwa [hcomm]
      · intro he
        have heBs : e ∈ Bs := by
          have : e = y'⁻¹ * (y' * e * y'⁻¹) * y' := by group
          rw [this]
          exact Bs.mul_mem (Bs.mul_mem (Bs.inv_mem hyB) (hE_le_Bs he)) hyB
        have h2 : y' * e = e * y' :=
          congrArg (fun x : ↥Bs => (x : G))
            ((isMulCommutative_iff.mp hBsab.1) ⟨y', hyB⟩ ⟨e, heBs⟩)
        have hcomm : y' * e * y'⁻¹ = e := by rw [h2]; group
        rwa [hcomm] at he
    have hcard_sup : Nat.card ↥(Subgroup.zpowers y' ⊔ E) = 7 ^ 4 := by
      have hset : ((Subgroup.zpowers y' ⊔ E : Subgroup G) : Set G) =
          (Subgroup.zpowers y' : Set G) * (E : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right (H := Subgroup.zpowers y') (N := E) hnorm
      let g : ↥(Subgroup.zpowers y') × ↥E → ↥(Subgroup.zpowers y' ⊔ E) :=
        fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      have hg_inj : Function.Injective g := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ h
        have hval : (a : G) * b = (a' : G) * b' := congrArg Subtype.val h
        have hkey : (a' : G)⁻¹ * a = (b' : G) * (b : G)⁻¹ := by
          calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * ((a : G) * b) * (b : G)⁻¹ := by group
            _ = (a' : G)⁻¹ * ((a' : G) * b') * (b : G)⁻¹ := by rw [hval]
            _ = (b' : G) * (b : G)⁻¹ := by group
        have h1 : (a' : G)⁻¹ * a ∈ Subgroup.zpowers y' :=
          (Subgroup.zpowers y').mul_mem ((Subgroup.zpowers y').inv_mem a'.2) a.2
        have h2 : (a' : G)⁻¹ * a ∈ E := by
          rw [hkey]
          exact E.mul_mem b'.2 (E.inv_mem b.2)
        have hone : (a' : G)⁻¹ * a = 1 := by
          have hmem : (a' : G)⁻¹ * a ∈ Subgroup.zpowers y' ⊓ E := ⟨h1, h2⟩
          rw [inf_comm, hy'E, Subgroup.mem_bot] at hmem
          exact hmem
        have haa : a = a' := Subtype.ext ((eq_of_inv_mul_eq_one hone).symm)
        have hbb : b = b' := by
          have hb : (b' : G) * (b : G)⁻¹ = 1 := hkey ▸ hone
          exact Subtype.ext (eq_of_mul_inv_eq_one hb).symm
        exact Prod.ext haa hbb
      have hg_surj : Function.Surjective g := by
        intro x
        have hx : (x : G) ∈ (Subgroup.zpowers y' : Set G) * (E : Set G) := by
          rw [← hset]; exact x.2
        obtain ⟨a, ha, b, hb, hab⟩ := hx
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by simpa [g] using Subtype.ext hab⟩
      have hcard := Nat.card_congr (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩)
      rw [← hcard, Nat.card_prod,
        show Nat.card ↥(Subgroup.zpowers y') = 7 from by
          rw [Nat.card_zpowers, orderOf_eq_prime hy7 hyne], hEcard]
      norm_num
    have hsup_le : Subgroup.zpowers y' ⊔ E ≤ Bs :=
      sup_le (Subgroup.zpowers_le.mpr hyB) hE_le_Bs
    have hle : Nat.card ↥Bs ≤ Nat.card ↥(Subgroup.zpowers y' ⊔ E) := by
      rw [hcardBs, hcard_sup]
    exact (Subgroup.eq_of_le_of_card_ge hsup_le hle).symm
  ·
    intro hyE
    have hyK : y' ∈ K' := hE_le_K' hyE
    have hyC : y' ∈ Subgroup.centralizer (K' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)
    have hz : (⟨y', hyK⟩ : ↥K') ∈ Z := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hyC (g : G) g.2
    have hdvd : 7 ∣ Nat.card Z := by
      rw [← orderOf_eq_prime hy7 hyne, Subgroup.orderOf_coe ⟨y', hyK⟩,
        Subgroup.orderOf_coe (⟨⟨y', hyK⟩, hz⟩ : Z)]
      exact orderOf_dvd_natCard _
    exact hZ hdvd

private theorem a11ss_not_dvd_A3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    ¬ 7 ^ 4 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
  have hadm : StatedLieAdmissible .PSL 4 2 3 := by
    simp only [StatedLieAdmissible]; norm_num
  have hmod : StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) .PSL 4 2 3 :=
    statedClassicalModel_linear 4 3 (by simpa using hK) hadm
  rw [card_eq_lieOrd_of_classical hmod]
  decide

private theorem a11ss_not_dvd_C3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    ¬ 7 ^ 4 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K 3)) := by
  have hadm : StatedLieAdmissible .PSp 3 2 3 := by
    simp only [StatedLieAdmissible]; norm_num
  have hmod : StatedClassicalModel (LargeEvenProj (LargeEvenSpGroup K 3)) .PSp 3 2 3 :=
    statedClassicalModel_symplectic 3 3 (by simpa using hK) hadm
  rw [card_eq_lieOrd_of_classical hmod]
  decide

private theorem a11ss_not_dvd_twD {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ 7 ^ 4 ∣ Nat.card (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus 3 b c))) := by
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 3 := by
    simp only [StatedLieAdmissible]; norm_num
  have hmod : StatedClassicalModel
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus 3 b c))) .POmegaMinus 4 2 3 :=
    statedClassicalModel_omegaMinus 4 3 (by simpa using hK) b c hbc hadm
  rw [card_eq_lieOrd_of_classical hmod]
  decide

private theorem a11ss_exists_not_dvd_A3 {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum ⟨.A, 3, 3⟩ Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F ∧ ¬ 7 ^ 4 ∣ Nat.card R := by
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at h
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨_, _, _, _, hQ, a11ss_not_dvd_A3 hK⟩

private theorem a11ss_exists_not_dvd_C3 {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum ⟨.C, 3, 3⟩ Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F ∧ ¬ 7 ^ 4 ∣ Nat.card R := by
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at h
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨_, _, _, _, hQ, a11ss_not_dvd_C3 hK⟩

private theorem a11ss_exists_not_dvd_twD {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum ⟨.twD, 4, 3⟩ Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F ∧ ¬ 7 ^ 4 ∣ Nat.card R := by
  dsimp only [LargeEvenRawDatum] at h
  rw [if_neg (by norm_num : ¬ (4 : ℕ) = 2), if_neg (by norm_num : ¬ (4 : ℕ) = 3)] at h
  norm_num at h
  dsimp only [LargeEvenRecipeOmegaMinus] at h
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  exact ⟨_, _, _, _, hQ, a11ss_not_dvd_twD hK b c hbc⟩

private def a11ss_labDisj (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.A, 3, 3⟩ ∨ lab = ⟨.C, 3, 3⟩ ∨ lab = ⟨.twD, 4, 3⟩

private theorem a11ss_exists_not_dvd {Q : LargeEvenRawCont} {lab : LargeEvenLabel}
    (h : LargeEvenRawDatum lab Q) (hlab : a11ss_labDisj lab) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F ∧ ¬ 7 ^ 4 ∣ Nat.card R := by
  rcases hlab with rfl | rfl | rfl
  · exact a11ss_exists_not_dvd_A3 h
  · exact a11ss_exists_not_dvd_C3 h
  · exact a11ss_exists_not_dvd_twD h
theorem a11SylowSplitInput_holds :
    A11SylowSplitInput := by
  intro hMp hLB hRig G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hhas
  obtain ⟨hRest, hA11, hFrame, hExtra, hCoh, hRho⟩ := hctx
  have hcfg : GGConfig 7 B Bs x L D J := hRest.1
  have hInnL : GGInnerDiagOn Bs L := hRest.2.2.1.1
  have hInn : GGInnerDiagOn Bs K' := hRest.2.2.1.2 y' K' hnb
  have hmodL : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 := hA11.2.1
  have hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    ggA8Nbr_bstar_inf_centralizer_J_le hMp hcfg hInnL hmodL hnb
  have hJK : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hExtra.1 hnb
  have hcardBs : Nat.card Bs = 7 ^ 4 := by
    rw [← hFrame.2.2.2.1]; exact hFrame.1.2.2.2.2.1
  have hfamA : GGL45NtFamCl 7 ⟨.A, 3, 3⟩ := by
    simp [GGL45NtFamCl, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel]
  have hkgA : GGL45KGLabel 7 ⟨.A, 3, 3⟩ := by simp [GGL45KGLabel]
  have hfamC : GGL45NtFamCl 7 ⟨.C, 3, 3⟩ := by
    simp [GGL45NtFamCl, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel]
  have hkgC : GGL45KGLabel 7 ⟨.C, 3, 3⟩ := by simp [GGL45KGLabel]
  have hfamD : GGL45NtFamCl 7 ⟨.twD, 4, 3⟩ := by
    simp [GGL45NtFamCl, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel]
  have hkgD : GGL45KGLabel 7 ⟨.twD, 4, 3⟩ := by simp [GGL45KGLabel]
  rcases hhas with hA | hC | hD
  · have hlab0 : LargeEvenInLambda2 ⟨.A, 3, 3⟩ := by
      simp only [LargeEvenInLambda2]; norm_num
    have hmark := ggInnerDiagOn_relabel hRig hInn hlab0 hA
    have hmark2 := largeEvenMarking_and_labelAll
      (P' := GGL45NtRec 7)
      (S := fun lab => GGL45NtFamCl 7 lab ∧ GGL45KGLabel 7 lab)
      (fun lab hlab hS => ggL45NtRecOn_cl 7 (by norm_num) (by norm_num) lab hlab hS.2 hS.1)
      (fun lab R _ I F θ hP => by rw [hP.1]; exact ⟨hfamA, hkgA⟩)
      hmark
    obtain ⟨hperf, lab, hlab, hraw⟩ := hmark2
    have hlab_eq : lab = ⟨.A, 3, 3⟩ := by
      obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
      obtain ⟨-, -, θ0, hP0, -⟩ := hQ0
      exact hP0.1
    obtain ⟨R, _, I, F, hQ, hRord⟩ := a11ss_exists_not_dvd hraw (Or.inl hlab_eq)
    obtain ⟨hs, hna, θ, hP, hrec⟩ := hQ
    exact a11ss_main hcfg hnb hP.2.1 hCJ hJK hcardBs I F θ hs hna hrec hP.2.2 hperf hRord
  · have hlab0 : LargeEvenInLambda2 ⟨.C, 3, 3⟩ := by
      simp only [LargeEvenInLambda2]; norm_num
    have hmark := ggInnerDiagOn_relabel hRig hInn hlab0 hC
    have hmark2 := largeEvenMarking_and_labelAll
      (P' := GGL45NtRec 7)
      (S := fun lab => GGL45NtFamCl 7 lab ∧ GGL45KGLabel 7 lab)
      (fun lab hlab hS => ggL45NtRecOn_cl 7 (by norm_num) (by norm_num) lab hlab hS.2 hS.1)
      (fun lab R _ I F θ hP => by rw [hP.1]; exact ⟨hfamC, hkgC⟩)
      hmark
    obtain ⟨hperf, lab, hlab, hraw⟩ := hmark2
    have hlab_eq : lab = ⟨.C, 3, 3⟩ := by
      obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
      obtain ⟨-, -, θ0, hP0, -⟩ := hQ0
      exact hP0.1
    obtain ⟨R, _, I, F, hQ, hRord⟩ := a11ss_exists_not_dvd hraw (Or.inr (Or.inl hlab_eq))
    obtain ⟨hs, hna, θ, hP, hrec⟩ := hQ
    exact a11ss_main hcfg hnb hP.2.1 hCJ hJK hcardBs I F θ hs hna hrec hP.2.2 hperf hRord
  · have hlab0 : LargeEvenInLambda2 ⟨.twD, 4, 3⟩ := by
      simp only [LargeEvenInLambda2]; norm_num
    have hmark := ggInnerDiagOn_relabel hRig hInn hlab0 hD
    have hmark2 := largeEvenMarking_and_labelAll
      (P' := GGL45NtRec 7)
      (S := fun lab => GGL45NtFamCl 7 lab ∧ GGL45KGLabel 7 lab)
      (fun lab hlab hS => ggL45NtRecOn_cl 7 (by norm_num) (by norm_num) lab hlab hS.2 hS.1)
      (fun lab R _ I F θ hP => by rw [hP.1]; exact ⟨hfamD, hkgD⟩)
      hmark
    obtain ⟨hperf, lab, hlab, hraw⟩ := hmark2
    have hlab_eq : lab = ⟨.twD, 4, 3⟩ := by
      obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
      obtain ⟨-, -, θ0, hP0, -⟩ := hQ0
      exact hP0.1
    obtain ⟨R, _, I, F, hQ, hRord⟩ := a11ss_exists_not_dvd hraw (Or.inr (Or.inr hlab_eq))
    obtain ⟨hs, hna, θ, hP, hrec⟩ := hQ
    exact a11ss_main hcfg hnb hP.2.1 hCJ hJK hcardBs I F θ hs hna hrec hP.2.2 hperf hRord

end CFSG.StandardType.A11

end
