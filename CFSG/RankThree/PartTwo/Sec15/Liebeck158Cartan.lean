module

public import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofTorus
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec15.Liebeck158TypeC
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck158

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec15.Proof158Cartan
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

variable {G : Type} [Group G] [Finite G]

theorem exists_cartan_of_card_nine {L P' : Subgroup G} {c : G} (hcL : c ∉ L) (hc3 : c ^ 3 = 1)
    (hLc : ∀ l ∈ L, l * c = c * l) (hP'N : P' ≤ Subgroup.normalizer (L : Set G))
    (hP'3 : IsPGroup 3 P') (hcP' : c ∈ P')
    (hmodL : ∀ a ∈ P', ∀ b ∈ P', a * b * a⁻¹ * b⁻¹ ∈ L) (hcubeL : ∀ a ∈ P', a ^ 3 ∈ L)
    (hker : ∀ a ∈ P', a ∈ thetaQuotCentralizer L → a ∈ Subgroup.zpowers c)
    (hP'81 : Nat.card P' = 81)
    (hcube : ∀ a ∈ P', a ^ 3 ∈ Subgroup.zpowers c)
    (hnc : ∃ a ∈ P', ∃ b ∈ P', a * b * a⁻¹ * b⁻¹ ∉ Subgroup.zpowers c)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f)
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K))
    (hA : ∀ (g : G) (hg : g ∈ P'), ∃ y ∈ glPi π 3 (p ^ f) K,
      ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      ((e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hP'N hg⟩) z) :
        ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ∃ E : Subgroup G, E ≤ P' ∧ c ∈ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      IsTypeCOn E L ∧ P' ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hP'N hcP'
  set ρ : ↥P' →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (actBar L).comp (Subgroup.inclusion hP'N)
  have hcρ : ρ ⟨c, hcP'⟩ = 1 := actBar_eq_one_of_commute hcN hLc
  have hkerle : ∀ g : ↥P', ρ g = 1 → (g : G) ∈ Subgroup.zpowers c := fun g hg =>
    hker g g.2 ((actBar_eq_one_iff _).mp hg)
  have hkerge : ∀ g : ↥P', (g : G) ∈ Subgroup.zpowers c → ρ g = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : g = ⟨c, hcP'⟩ ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow, hcρ, _root_.one_zpow]
  have hker3 : Nat.card ρ.ker = 3 := by
    have hle : ρ.ker ≤ (Subgroup.zpowers c).subgroupOf P' := fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hkerle g hg)
    have hge : (Subgroup.zpowers c).subgroupOf P' ≤ ρ.ker := fun g hg =>
      hkerge g (Subgroup.mem_subgroupOf.mp hg)
    rw [le_antisymm hle hge, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hcP')).toEquiv, Sec13.card_zpowers_of_pow_three hc3 hc1]
  have hR27 : Nat.card ρ.range = 27 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hker3, hP'81] at h1
    omega
  have hRp : IsPGroup 3 ρ.range := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk⟩ := hP'3 g
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← map_pow, hk, map_one, Subgroup.coe_one]
  have hRexp : ∀ σ ∈ ρ.range, σ ^ 3 = 1 := by
    rintro _ ⟨g, rfl⟩
    rw [← map_pow]
    exact hkerge _ (by rw [Subgroup.coe_pow]; exact hcube g g.2)
  have hRnc : ¬ IsMulCommutative ρ.range := by
    intro hcomm
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have h1 : ρ (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
      have h2 : ρ ⟨a, ha⟩ * ρ ⟨b, hb⟩ = ρ ⟨b, hb⟩ * ρ ⟨a, ha⟩ :=
        congrArg Subtype.val (hcomm.is_comm.comm ⟨ρ ⟨a, ha⟩, ⟨_, rfl⟩⟩ ⟨ρ ⟨b, hb⟩, ⟨_, rfl⟩⟩)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
      group
    exact hab (hkerle _ h1)
  have hRA : ∀ σ ∈ ρ.range, ∃ y ∈ glPi π 3 (p ^ f) K,
      ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      ((e (σ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ := by
    rintro _ ⟨g, rfl⟩
    exact hA g g.2
  obtain ⟨P₀, hP₀R, hP₀9, D, hDC, hP₀D, hDP₀⟩ :=
    exists_typeC_of_nonabelian hK hq hq2 e ρ.range hRp hR27 hRnc hRexp hRA
  have hP₀3 : ∀ τ ∈ P₀, τ ^ 3 = 1 := by
    intro τ hτ
    obtain ⟨y, hyD, hy⟩ := hP₀D τ hτ
    obtain ⟨μ, hμ⟩ := hDC.2.1 y hyD
    have hmk : ProjGenLinGroup.mk y ^ 3 = 1 := by
      rw [← map_pow, ← hμ]
      exact (mk_eq_one_iff_mem_statedScalars).mpr ⟨μ, rfl⟩
    ext z
    apply e.injective
    apply Subtype.ext
    rw [MulAut.one_apply]
    have key : ∀ (n : ℕ) (w : ↥L ⧸ aschbacherSolvableCore 3 ↥L),
        ((e ((τ ^ n) w) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y ^ n * (e w : ProjGenLinGroup (Fin 3) K) *
            (ProjGenLinGroup.mk y ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ, MulAut.mul_apply, ih, hy, pow_succ]
        group
    rw [key 3 z, hmk, one_mul, inv_one, mul_one]
  have hP₀comm : ∀ τ₁ ∈ P₀, ∀ τ₂ ∈ P₀, τ₁ * τ₂ = τ₂ * τ₁ := by
    have hP₀p : IsPGroup 3 P₀ := IsPGroup.of_card (n := 2) (by rw [hP₀9]; norm_num)
    have : IsMulCommutative P₀ := by
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P₀)
        (by rw [hP₀9]; norm_num)
    intro τ₁ h₁ τ₂ h₂
    exact congrArg Subtype.val (this.is_comm.comm ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩)
  set E' : Subgroup ↥P' := P₀.comap ρ with hE'
  set E : Subgroup G := E'.map P'.subtype with hE
  have hEP : E ≤ P' := Subgroup.map_subtype_le E'
  have hmemE : ∀ g : ↥P', (g : G) ∈ E ↔ ρ g ∈ P₀ := fun g => by
    constructor
    · rintro ⟨g', hg', hgg'⟩
      rwa [show g = g' from Subtype.ext hgg'.symm]
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hmemE' : ∀ g : ↥P', (g : G) ∈ E ↔ g ∈ E' := fun g => by
    rw [hmemE, hE', Subgroup.mem_comap]
  have hE'map : E'.map ρ = P₀ := by
    rw [hE', Subgroup.map_comap_eq, inf_eq_right.mpr hP₀R]
  have hkerE' : ρ.ker ≤ E' := fun g hg => by
    rw [MonoidHom.mem_ker] at hg
    change ρ g ∈ P₀
    rw [hg]
    exact P₀.one_mem
  have hE'27 : Nat.card E' = 27 := by
    have h1 := Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf ρ E'
    rw [hE'map, hP₀9] at h1
    have h2 : Nat.card (ρ.ker.subgroupOf E') = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerE').toEquiv, hker3]
    rw [h2] at h1
    omega
  have hE27 : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective P'.subtype_injective, hE'27]
  have hcE : c ∈ E := (hmemE ⟨c, hcP'⟩).mpr (by rw [hcρ]; exact P₀.one_mem)
  have htriv : ∀ g : ↥P', ρ g = 1 → (g : G) ∈ L → g = 1 := by
    intro g h1 h2
    have hg : (g : G) ∈ Subgroup.zpowers c ⊓ L := ⟨hkerle g h1, h2⟩
    rw [Sec13.zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at hg
    exact Subtype.ext hg
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
    · have ha := (hmemE ⟨a, hEP a.2⟩).mp a.2
      have hb := (hmemE ⟨b, hEP b.2⟩).mp b.2
      have h1 : (⟨a, hEP a.2⟩ : ↥P') * ⟨b, hEP b.2⟩ * (⟨a, hEP a.2⟩ : ↥P')⁻¹ *
          (⟨b, hEP b.2⟩ : ↥P')⁻¹ = 1 := htriv _
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hP₀comm _ ha _ hb]; group)
        (hmodL a (hEP a.2) b (hEP b.2))
      have h2 : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = 1 := by
        have h3 := congrArg Subtype.val h1
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using h3
      calc (a : G) * (b : G) =
          ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by group
        _ = (b : G) * (a : G) := by rw [h2, one_mul]
    · have h1 : (⟨g, hEP hg⟩ : ↥P') ^ 3 = 1 := htriv _
        (by rw [map_pow]; exact hP₀3 _ ((hmemE _).mp hg))
        (by simpa using hcubeL g (hEP hg))
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hsec : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf (hEP.trans hP'N)]
    ext a
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨haE, haC⟩
      exact hker a (hEP haE) haC
    · intro ha
      refine ⟨Subgroup.zpowers_le.mpr hcE ha, ?_⟩
      have hcT : c ∈ thetaQuotCentralizer L :=
        (actBar_eq_one_iff ⟨c, hcN⟩).mp (actBar_eq_one_of_commute hcN hLc)
      exact Subgroup.zpowers_le.mpr hcT ha
  have hTC : IsTypeCOn E L := by
    refine ⟨π, p, f, K, inferInstance, hK, hq, e, D, hDC, ?_, ?_⟩
    · intro τ hτ
      obtain ⟨h, hN, hhE, rfl⟩ := mem_autThetaQuot_iff.mp hτ
      have hρh : ρ ⟨h, hEP hhE⟩ ∈ P₀ := (hmemE ⟨h, hEP hhE⟩).mp hhE
      obtain ⟨y, hyD, hy⟩ := hP₀D _ hρh
      exact ⟨y, hyD, fun z => hy z⟩
    · intro y hyD
      obtain ⟨τ, hτP₀, hτ⟩ := hDP₀ y hyD
      obtain ⟨g, hg⟩ := hP₀R hτP₀
      refine ⟨τ, mem_autThetaQuot_iff.mpr ⟨g, hP'N g.2, (hmemE g).mpr (hg ▸ hτP₀), ?_⟩, hτ⟩
      rw [← hg]
      rfl
  have hnorm : E'.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    have h1 := Subgroup.card_mul_index E'
    rw [hE'27, hP'81] at h1
    have h3 : E'.index = 3 := by omega
    rw [h3, hP'81]
    norm_num
  clear_value E E' ρ
  have hPN : P' ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxP : x ∈ P' := hEP hx
      have h0 : (⟨x, hxP⟩ : ↥P') ∈ E' := (hmemE' ⟨x, hxP⟩).mp hx
      have h1 := (hmemE' (⟨g, hg⟩ * ⟨x, hxP⟩ * ⟨g, hg⟩⁻¹)).mpr (hnorm.conj_mem _ h0 ⟨g, hg⟩)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · intro hx
      have h1 : g * x * g⁻¹ ∈ P' := hEP hx
      have hxP : x ∈ P' := by
        have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ P' :=
          P'.mul_mem (P'.mul_mem (P'.inv_mem hg) h1) (P'.inv_mem (P'.inv_mem hg))
        simpa [mul_assoc] using h2
      have h0 : (⟨g * x * g⁻¹, h1⟩ : ↥P') ∈ E' := (hmemE' ⟨g * x * g⁻¹, h1⟩).mp hx
      have h3 := hnorm.conj_mem _ h0 (⟨g, hg⟩⁻¹ : ↥P')
      have h4 : (⟨g, hg⟩⁻¹ : ↥P') * ⟨g * x * g⁻¹, h1⟩ * (⟨g, hg⟩⁻¹ : ↥P')⁻¹ = ⟨x, hxP⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]; group)
      rw [h4] at h3
      exact (hmemE' ⟨x, hxP⟩).mpr h3
  exact ⟨E, hEP, hcE, hEab, hE27, hsec, hTC, hPN⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck158
