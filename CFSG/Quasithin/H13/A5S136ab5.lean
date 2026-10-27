module

public import CFSG.Quasithin.H13.A5S136abQ
public import CFSG.Quasithin.H13.A5S136ab3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd pRank_subgroupOf_eq)

namespace ConfAB

theorem exists_starEquiv {H : Type} [Group H] [Finite H] {L : Subgroup H} (hLn : L.Normal)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥)
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ θ : ↥(starImage 3 L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L), ∀ x : ↥L,
      θ ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (x : H), Subgroup.mem_map_of_mem _ x.2⟩ =
        (x : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ₀ : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ₀
  set π₃ := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ₃
  let ρ : ↥L →* ↥(starImage 3 L) :=
    (π₃.comp L.subtype).codRestrict (starImage 3 L) (fun x => Subgroup.mem_map_of_mem _ x.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : ↥L, x ∈ ρ.ker → (x : H) ∈ CFSG.pPrimeCore 3 H := by
    intro x hx
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change π₃ (x : H) = 1 at h1
    rwa [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hN3 : Nat.Coprime 3 (Nat.card ρ.ker) := by
    have hle : ρ.ker.map L.subtype ≤ CFSG.pPrimeCore 3 H := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hNX : ρ.ker.map φ₀ = ⊥ := by
    have hn : (ρ.ker.map φ₀).Normal :=
      Subgroup.Normal.map inferInstance φ₀ (QuotientGroup.mk'_surjective _)
    have hne : ρ.ker.map φ₀ ≠ ⊤ := by
      intro htop
      have h1 : Nat.card (ρ.ker.map φ₀) ∣ Nat.card ρ.ker := by
        rw [← MonoidHom.domRestrict_range]
        exact card_range_dvd _
      rw [htop, Subgroup.card_top] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right h1 hN3) h3)
        (by norm_num)
    have hle := le_center_of_normal_ne_top hQ hne
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  have hle : ρ.ker ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    have : φ₀ x ∈ ρ.ker.map φ₀ := Subgroup.mem_map_of_mem φ₀ hx
    rw [hNX, Subgroup.mem_bot, hφ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have hge : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    have hNL : ∀ g : H, g ∈ Subgroup.normalizer (L : Set H) := fun g => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact hLn.conj_mem h hh g
      · intro hh
        have := hLn.conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this
    have hN : (CFSG.Open.pCoreOf 2 L).Normal := ⟨fun n hn g =>
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hNL g)) n).mp hn⟩
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.Open.pCoreOf 2 L)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hO : CFSG.Open.pCoreOf 2 L ≤ CFSG.pPrimeCore 3 H := le_sSup ⟨hN, hcop⟩
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show π₃ (x : H) = 1
    rw [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hO ((AppC.mem_pCore_iff_mem_blockQ x).mp hx)
  have hkerEq : ρ.ker = CFSG.pCore 2 ↥L := le_antisymm hle hge
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkerEq), fun x => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm (ρ x) =
      (x : ↥L ⧸ ρ.ker) := (MulEquiv.symm_apply_eq _).mpr rfl
  show QuotientGroup.quotientMulEquivOfEq hkerEq
    ((QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm (ρ x)) = _
  rw [h1]
  rfl

theorem card_eq_of_isPSLEps3 {s : Bool} {e : ℕ} {X Y : Type} [Group X] [Group Y]
    (hX : CFSG.Quasithin.IsPSLEps3 s 2 e X) (hY : CFSG.Quasithin.IsPSLEps3 s 2 e Y) :
    Nat.card X = Nat.card Y := by
  cases s
  · obtain ⟨⟨-, he, -⟩, F, _, _, hF, ⟨eX⟩⟩ := hX
    obtain ⟨-, F', _, _, hF', ⟨eY⟩⟩ := hY
    rw [Nat.card_congr eX.toEquiv, Nat.card_congr eY.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two he hF (by norm_num),
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two he hF' (by norm_num)]
  · obtain ⟨-, F, _, _, hF, ⟨eX⟩⟩ := hX
    obtain ⟨-, F', _, _, hF', ⟨eY⟩⟩ := hY
    rw [Nat.card_congr eX.toEquiv, Nat.card_congr eY.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3),
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF, hF']

theorem oPrimeResidualOf_three_top_normal {X : Type*} [Group X] :
    (oPrimeResidualOf 3 (⊤ : Subgroup X)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨-, k, hk⟩ := hy
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, k, ?_⟩
    rw [← MulAut.conj_apply]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hk
  | one => simp
  | mul a b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group] at this
  | inv a _ ha =>
    have := Subgroup.inv_mem _ ha
    rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at this

theorem oPrimeResidualOf_three_top_eq_top {X : Type*} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥) (h3 : 3 ∣ Nat.card X) :
    oPrimeResidualOf 3 (⊤ : Subgroup X) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := oPrimeResidualOf_three_top_normal (X := X)
  by_contra hne
  have hle := le_center_of_normal_ne_top hq hne
  rw [hZ] at hle
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  have hxm : x ∈ oPrimeResidualOf 3 (⊤ : Subgroup X) :=
    Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [hx, pow_one]⟩
  have h1 := Subgroup.mem_bot.mp (hle hxm)
  rw [h1, orderOf_one] at hx
  omega

theorem mul_conj_mul_inv {X : Type*} [Group X] (φ : MulAut X) (g : X) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  show φ (g * φ⁻¹ x * g⁻¹) = φ g * x * (φ g)⁻¹
  rw [map_mul, map_mul, map_inv]
  congr 2
  exact MulEquiv.apply_symm_apply φ x

theorem apply_eq_of_commute_conj {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    {φ : MulAut X} {u : X} (h : φ * MulAut.conj u = MulAut.conj u * φ) : φ u = u := by
  have h1 : MulAut.conj (φ u) = MulAut.conj u := by
    rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]
  have h2 : (φ u)⁻¹ * u ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun f : MulAut X => f g) h1
    simp only [MulAut.conj_apply] at this
    calc g * ((φ u)⁻¹ * u) = (φ u)⁻¹ * (φ u * g * (φ u)⁻¹) * u := by group
      _ = (φ u)⁻¹ * (u * g * u⁻¹) * u := by rw [this]
      _ = (φ u)⁻¹ * u * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem commute_conj_of_apply_eq {X : Type*} [Group X] {φ : MulAut X} {x : X} (h : φ x = x) :
    φ * MulAut.conj x = MulAut.conj x * φ := by
  have h1 := mul_conj_mul_inv φ x
  rw [h] at h1
  calc φ * MulAut.conj x = φ * MulAut.conj x * φ⁻¹ * φ := by group
    _ = MulAut.conj x * φ := by rw [h1]

theorem mem_sylow_of_commute {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) {x : X}
    (hx : x * x = 1) (hc : ∀ t ∈ (P : Subgroup X), x * t = t * x) : x ∈ (P : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := if x = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    split_ifs with h
    · rw [h, orderOf_one, pow_zero]
    · rw [pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact hx) h
  have hN : (P : Subgroup X) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
    intro t ht
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (hc t ht) k).eq)
  have hsup : IsPGroup 2 ↥((P : Subgroup X) ⊔ Subgroup.zpowers x) :=
    IsPGroup.to_sup_of_normal_right' P.isPGroup' hZ2 hN
  have heq := P.is_maximal' hsup le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem indHom_commute_of_mem_centralizer {G : Type} [Group G] {K : Subgroup G} {X : Type}
    [Group X] (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) {c d : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hdN : d ∈ Subgroup.normalizer (K : Set G))
    (h : c * d * c⁻¹ * d⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    indHom K ψ ⟨c, hcN⟩ * indHom K ψ ⟨d, hdN⟩ = indHom K ψ ⟨d, hdN⟩ * indHom K ψ ⟨c, hcN⟩ := by
  have hN : c * d * c⁻¹ * d⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer _ h
  have e : (⟨c * d * c⁻¹ * d⁻¹, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨c, hcN⟩ * ⟨d, hdN⟩ * (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ *
        (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
  have h1 := indHom_eq_one_of_mem_centralizer K ψ (c := ⟨_, hN⟩) h
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc indHom K ψ ⟨c, hcN⟩ * indHom K ψ ⟨d, hdN⟩ =
        (indHom K ψ ⟨c, hcN⟩ * indHom K ψ ⟨d, hdN⟩ * (indHom K ψ ⟨c, hcN⟩)⁻¹ *
          (indHom K ψ ⟨d, hdN⟩)⁻¹) * indHom K ψ ⟨d, hdN⟩ * indHom K ψ ⟨c, hcN⟩ := by group
    _ = indHom K ψ ⟨d, hdN⟩ * indHom K ψ ⟨c, hcN⟩ := by rw [h1, one_mul]

theorem comm_mem_centralizer_of_indHom_commute {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hqs : CFSG.IsQuasisimple ↥K) {X : Type} [Group X] (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X)
    {c d : G} (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hdN : d ∈ Subgroup.normalizer (K : Set G))
    (h : indHom K ψ ⟨c, hcN⟩ * indHom K ψ ⟨d, hdN⟩ = indHom K ψ ⟨d, hdN⟩ * indHom K ψ ⟨c, hcN⟩) :
    c * d * c⁻¹ * d⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  have hN : c * d * c⁻¹ * d⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hdN)
      (Subgroup.inv_mem _ hcN)) (Subgroup.inv_mem _ hdN)
  have e : (⟨c * d * c⁻¹ * d⁻¹, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨c, hcN⟩ * ⟨d, hdN⟩ * (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ *
        (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
  refine mem_centralizer_of_indHom_eq_one hqs ψ (c := ⟨_, hN⟩) ?_
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

end ConfAB

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem inner_of_case2 (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (hF3 : FactLieZCentPGL3) (hF6 : FactL3SylowCenterCyclic) (hEven : Ch1.EvenLieAutInner)
    (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))
    (hr : 1 < CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hSQ : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K))
    {X Q : Subgroup G} {y : G} (hyLv : y ∈ S.Lv) (hconf : Conf1366 K X Q S.a S.z y)
    (h2 : A318Case2 (starImage 3 (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G)))))
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K, ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ = MulAut.conj k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have hGvS : SQTKGroup ↥Gv :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian S.pCoreOf_Gv_ne_bot'
  have hSQ' := SQTKHyp.of_sqtkGroup ↥Gv hGvS
  have hLc := subgroupOf_mem_cComp hKc
  set K' : Subgroup ↥Gv := K.subgroupOf Gv with hK'
  let e₁ : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKG
  have hmap : (CFSG.pCore 2 ↥K').map (e₁ : ↥K' →* ↥K) = CFSG.pCore 2 ↥K := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e₁
    exact this
  let e₀ : (↥K' ⧸ CFSG.pCore 2 ↥K') ≃* (↥K ⧸ CFSG.pCore 2 ↥K) := QuotientGroup.congr _ _ e₁ hmap
  have hQ' : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hZ' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥ := by
    have h1 := Subgroup.map_center_eq e₀
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).mp h1
  have h3' : 3 ∣ Nat.card (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    rw [Nat.card_congr e₀.toEquiv]
    exact h3
  have hr1 : 1 < CFSG.Open.pRank 3 K' := by
    rw [pRank_subgroupOf_eq hKG Nat.prime_three (by norm_num)]
    exact hr
  have hK'n : K'.Normal :=
    A318.normal_of_pRank_gt_one hGvS ((a38ForSQTK_of_cat h38) _ hSQ') hLc Nat.prime_three
      (by norm_num) hr1
  obtain ⟨θ, hθ⟩ := ConfAB.exists_starEquiv hK'n hQ' hZ' h3'
  let π₃ : ↥Gv →* PStar 3 ↥Gv := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Gv)
  let Ks : Subgroup (PStar 3 ↥Gv) := starImage 3 K'
  let Θ : ↥Ks ≃* (↥K ⧸ CFSG.pCore 2 ↥K) := θ.trans e₀
  have hmemKs : ∀ (k : G) (hk : k ∈ K), π₃ ⟨k, hKG hk⟩ ∈ Ks := fun k hk =>
    Subgroup.mem_map_of_mem _ (show (⟨k, hKG hk⟩ : ↥Gv) ∈ K' from hk)
  have hΘ : ∀ (k : G) (hk : k ∈ K), Θ ⟨π₃ ⟨k, hKG hk⟩, hmemKs k hk⟩ =
      ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro k hk
    exact (congrArg e₀ (hθ ⟨⟨k, hKG hk⟩, hk⟩)).trans rfl
  have hKsn : Ks.Normal := hK'n.map π₃ (QuotientGroup.mk'_surjective _)
  have hΘc : ∀ (g : G) (hg : g ∈ Gv) (hgN : g ∈ Subgroup.normalizer (K : Set G)) (κ : ↥Ks),
      Θ ⟨π₃ ⟨g, hg⟩ * κ * (π₃ ⟨g, hg⟩)⁻¹, hKsn.conj_mem _ κ.2 _⟩ =
        ConfAB.indHom K (MulEquiv.refl _) ⟨g, hgN⟩ (Θ κ) := by
    intro g hg hgN κ
    obtain ⟨⟨k, hkGv⟩, hk, hκ⟩ := κ.2
    have hk' : k ∈ K := hk
    have hκ' : κ = ⟨π₃ ⟨k, hKG hk'⟩, hmemKs k hk'⟩ := Subtype.ext hκ.symm
    have hgk : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgN k).mp hk'
    have e2 : π₃ ⟨g, hg⟩ * κ * (π₃ ⟨g, hg⟩)⁻¹ = π₃ ⟨g * k * g⁻¹, hKG hgk⟩ := by
      rw [hκ']
      show π₃ ⟨g, hg⟩ * π₃ ⟨k, hKG hk'⟩ * (π₃ ⟨g, hg⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e3 : (⟨π₃ ⟨g, hg⟩ * κ * (π₃ ⟨g, hg⟩)⁻¹, hKsn.conj_mem _ κ.2 _⟩ : ↥Ks) =
        ⟨π₃ ⟨g * k * g⁻¹, hKG hgk⟩, hmemKs _ hgk⟩ := Subtype.ext e2
    rw [e3, hΘ _ hgk, hκ', hΘ _ hk']
    exact (ConfAB.indHom_apply K (MulEquiv.refl (↥K ⧸ CFSG.pCore 2 ↥K)) ⟨g, hgN⟩ ⟨k, hk'⟩).symm
  have hinn : ∀ β : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K), (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 (↥K ⧸ CFSG.pCore 2 ↥K), ∀ t ∈ (P : Subgroup _), β t = t) →
        Ch1.IsInnerAut β := fun β hβ hP => hEven _ hSQ β hβ hP
  obtain ⟨P, u, w, haN, hzN, hu, hw, hu1, hw1, huw, hγa, hγz⟩ :=
    ConfAB.exists_conj_of_conf hqs (MulEquiv.refl _) hinn hconf
  have hnc : ¬ IsCyclic (Subgroup.center ↥(P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) := by
    intro hc
    have h1mem : (1 : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ KG68.omegaZ (P : Subgroup _) :=
      KG68.mem_omegaZ_of_commute P (fun t _ => by rw [one_mul, mul_one]) (one_mul 1)
    exact ConfSpor.false_of_three_le (KG68.card_omegaZ_le_two (P : Subgroup _) hc) h1mem hu hw
      (Ne.symm hu1) (Ne.symm hw1) huw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hyodd, hya, hyz⟩ := hconf
  obtain ⟨s, q, hmod, ⟨p, e, hp, he, hqe, hPSL⟩, hX⟩ := h2
  have hpe : p = 2 ∧ 2 ≤ e := by
    by_contra hcon
    have hor : p ≠ 2 ∨ e = 1 := by
      by_cases hp2 : p = 2
      · right
        have : ¬ 2 ≤ e := fun h => hcon ⟨hp2, h⟩
        omega
      · exact Or.inl hp2
    have hcyc := hF6 s p e hp he hor ↥Ks hPSL
    apply hnc
    have hc := hcyc (P.mapSurjective (f := Θ.symm.toMonoidHom) Θ.symm.surjective)
    let E : ↥(P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
        ↥((P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)).map Θ.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ Θ.symm.injective
    have hc' : IsCyclic (Subgroup.center ↥((P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)).map
        Θ.symm.toMonoidHom)) := hc
    exact isCyclic_of_surjective (Subgroup.centerCongr E).symm.toMonoidHom
      (Subgroup.centerCongr E).symm.surjective
  obtain ⟨rfl, he2⟩ := hpe
  subst hqe
  set Xb := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 ↥Gv)) with hXb
  have hXbn : Xb.Normal := ConfAB.oPrimeResidualOf_three_top_normal
  have hgen := ConfAB.oPrimeResidualOf_three_top_eq_top hq hZ h3
  have hKsX : Ks ≤ Xb := by
    intro κ hκ
    set Y : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := (Xb.comap Ks.subtype).map Θ.toMonoidHom with hY
    have hle : oPrimeResidualOf 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ Y := by
      rw [oPrimeResidualOf, Subgroup.closure_le]
      rintro x ⟨-, k, hk⟩
      refine ⟨Θ.symm x, ?_, by simp⟩
      show ((Θ.symm x : ↥Ks) : PStar 3 ↥Gv) ∈ Xb
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, k, ?_⟩
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hk]
    rw [hgen] at hle
    obtain ⟨κ', hκ', he⟩ := hle (Subgroup.mem_top (Θ ⟨κ, hκ⟩))
    have h1 : (κ' : PStar 3 ↥Gv) = κ := congrArg Subtype.val (Θ.injective he)
    rw [← h1]
    exact hκ'
  have hGvN : Gv ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hK'n
  have hyGv : y ∈ Gv := (oTwoRes_le _ hyLv).2
  have hy3 : y ^ 3 = 1 := S.pow_three_eq_one_of_mem_Lv hyLv hyodd
  have hvC : ∀ k : ℤ, S.v12 ^ k ∈ Subgroup.centralizer (K : Set G) := by
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hKG hx)) k).eq
  set yb := π₃ ⟨y, hyGv⟩ with hyb
  have hyb3 : yb ^ 3 = 1 := by
    have h1 : (⟨y, hyGv⟩ : ↥Gv) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [hyb, ← map_pow, h1, map_one]
  have hybX : yb ∈ Xb := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hyb3) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hβu : ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ u = u := by
    refine ConfAB.apply_eq_of_commute_conj hZ ?_
    rw [← hγa]
    exact ConfAB.indHom_commute_of_mem_centralizer _ hyN haN hya
  have hfix : ∀ (g : G) (hg : g ∈ Gv) (x : ↥K ⧸ CFSG.pCore 2 ↥K),
      ConfAB.indHom K (MulEquiv.refl _) ⟨g, hGvN hg⟩ x = x →
        π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv) = (Θ.symm x : PStar 3 ↥Gv) * π₃ ⟨g, hg⟩ := by
    intro g hg x hx
    have h1 := hΘc g hg (hGvN hg) (Θ.symm x)
    rw [MulEquiv.apply_symm_apply, hx] at h1
    have h1' := congrArg Θ.symm h1
    rw [MulEquiv.symm_apply_apply] at h1'
    have h2 : π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv) * (π₃ ⟨g, hg⟩)⁻¹ =
        (Θ.symm x : PStar 3 ↥Gv) := congrArg Subtype.val h1'
    calc π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv)
        = (π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv) * (π₃ ⟨g, hg⟩)⁻¹) * π₃ ⟨g, hg⟩ := by group
      _ = (Θ.symm x : PStar 3 ↥Gv) * π₃ ⟨g, hg⟩ := by rw [h2]
  rcases hX with hPGL | ⟨m, -, hcirc⟩
  ·
    exfalso
    have hTv : IsSylowTwoOf S.Tv Gv :=
      S.isSylowTwoOf_centralizer h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
    set Tb : Subgroup (PStar 3 ↥Gv) := (S.Tv.subgroupOf Gv).map π₃ with hTb
    have hTbS : IsSylowTwoOf Tb ⊤ := by
      refine ⟨le_top, (hTv.2.1.comap_subtype).map _, fun h2 => hTv.2.2 ?_⟩
      have h1 : (Tb.subgroupOf ⊤).index = Tb.index := Subgroup.relIndex_top_right Tb
      have h4 : Tb.index ∣ (S.Tv.subgroupOf Gv).index :=
        Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
      rw [h1] at h2
      exact dvd_trans h2 h4
    have hXbN : (⊤ : Subgroup (PStar 3 ↥Gv)) ≤ Subgroup.normalizer (Xb : Set (PStar 3 ↥Gv)) :=
      fun g _ => Subgroup.mem_normalizer_iff.mpr fun x =>
        ⟨fun hx => hXbn.conj_mem x hx g, fun hx => by
          simpa [mul_assoc] using hXbn.conj_mem _ hx g⁻¹⟩
    obtain ⟨Pb, hPb⟩ := KGL33.exists_sylow_le le_top hXbN hTbS
    have hPbT : ∀ t ∈ (Pb : Subgroup ↥Xb), ∃ (t₀ : G) (ht₀ : t₀ ∈ Gv), t₀ ∈ S.Tv ∧
        (t : PStar 3 ↥Gv) = π₃ ⟨t₀, ht₀⟩ := by
      intro t ht
      obtain ⟨⟨t₀, ht₀⟩, ht₀T, he⟩ := hPb t ht
      exact ⟨t₀, ht₀, ht₀T, he.symm⟩
    set ub : ↥Xb := ⟨(Θ.symm u : PStar 3 ↥Gv), hKsX (Θ.symm u).2⟩ with hub
    set wb : ↥Xb := ⟨(Θ.symm w : PStar 3 ↥Gv), hKsX (Θ.symm w).2⟩ with hwb
    set kb : ↥Xb := ⟨yb, hybX⟩ with hkb
    have hubC : ∀ t ∈ (Pb : Subgroup ↥Xb), ub * t = t * ub := by
      intro t ht
      obtain ⟨t₀, ht₀, ht₀T, he⟩ := hPbT t ht
      have hc : ConfAB.indHom K (MulEquiv.refl _) ⟨t₀, hGvN ht₀⟩ u = u := by
        refine ConfAB.apply_eq_of_commute_conj hZ ?_
        rw [← hγa]
        have hC : S.a * t₀ * S.a⁻¹ * t₀⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv ht₀T)
          rw [← hk]
          exact hvC k
        exact (ConfAB.indHom_commute_of_mem_centralizer _ haN (hGvN ht₀) hC).symm
      have h1 := hfix t₀ ht₀ u hc
      apply Subtype.ext
      show (Θ.symm u : PStar 3 ↥Gv) * t = t * (Θ.symm u : PStar 3 ↥Gv)
      rw [he]
      exact h1.symm
    have hwbC : ∀ t ∈ (Pb : Subgroup ↥Xb), wb * t = t * wb := by
      intro t ht
      obtain ⟨t₀, ht₀, ht₀T, he⟩ := hPbT t ht
      have hc : ConfAB.indHom K (MulEquiv.refl _) ⟨t₀, hGvN ht₀⟩ w = w := by
        refine ConfAB.apply_eq_of_commute_conj hZ ?_
        rw [← hγz]
        have hC : S.z * t₀ * S.z⁻¹ * t₀⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
          have h1 := S.conj_z_of_mem_T ht₀T.1
          have h2 : S.z * t₀ * S.z⁻¹ * t₀⁻¹ = 1 := by
            calc S.z * t₀ * S.z⁻¹ * t₀⁻¹ = S.z * (t₀ * S.z * t₀⁻¹)⁻¹ := by group
              _ = 1 := by rw [h1]; group
          rw [h2]
          exact Subgroup.one_mem _
        exact (ConfAB.indHom_commute_of_mem_centralizer _ hzN (hGvN ht₀) hC).symm
      have h1 := hfix t₀ ht₀ w hc
      apply Subtype.ext
      show (Θ.symm w : PStar 3 ↥Gv) * t = t * (Θ.symm w : PStar 3 ↥Gv)
      rw [he]
      exact h1.symm
    have hsq : ∀ x : ↥K ⧸ CFSG.pCore 2 ↥K, x * x = 1 →
        (⟨(Θ.symm x : PStar 3 ↥Gv), hKsX (Θ.symm x).2⟩ : ↥Xb) *
          ⟨(Θ.symm x : PStar 3 ↥Gv), hKsX (Θ.symm x).2⟩ = 1 := by
      intro x hx
      apply Subtype.ext
      show ((Θ.symm x * Θ.symm x : ↥Ks) : PStar 3 ↥Gv) = 1
      rw [← map_mul, hx, map_one]
      rfl
    have hubP := ConfAB.mem_sylow_of_commute Pb (hsq u hu.2.2) hubC
    have hwbP := ConfAB.mem_sylow_of_commute Pb (hsq w hw.2.2) hwbC
    have hub1 : ub ≠ 1 := by
      intro h
      apply hu1
      have h1 : (Θ.symm u : PStar 3 ↥Gv) = 1 := congrArg Subtype.val h
      have h2 : Θ.symm u = 1 := Subtype.ext h1
      simpa using congrArg Θ h2
    have hkb3 : kb ^ 3 = 1 := Subtype.ext (by simpa [hkb] using hyb3)
    have hkbodd : Odd (orderOf kb) :=
      Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hkb3)
    have hkbub : kb * ub = ub * kb := Subtype.ext (hfix y hyGv u hβu)
    have hkw := hF3 s e he2 ↥Xb hPGL Pb ub wb kb hubP hubC hub1 hwbP hwbC hkbodd hkbub
    have h1 : yb * (Θ.symm w : PStar 3 ↥Gv) * yb⁻¹ = (Θ.symm w : PStar 3 ↥Gv) := by
      have := congrArg Subtype.val hkw
      simp only [hkb, hwb, Subgroup.coe_mul] at this
      rw [this]
      group
    have h2 := hΘc y hyGv hyN (Θ.symm w)
    have h3 : (⟨yb * (Θ.symm w : PStar 3 ↥Gv) * yb⁻¹, hKsn.conj_mem _ (Θ.symm w).2 _⟩ : ↥Ks) =
        Θ.symm w := Subtype.ext h1
    rw [h3, MulEquiv.apply_symm_apply] at h2
    have hβw : ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ w = w := h2.symm
    apply hyz
    refine ConfAB.comm_mem_centralizer_of_indHom_commute hqs (MulEquiv.refl _) hyN hzN ?_
    rw [hγz]
    exact ConfAB.commute_conj_of_apply_eq hβw
  ·
    obtain ⟨e', L₀, hL₀n, hq', hPSL₀, hcard3, -, h3L₀⟩ := hcirc
    have hee : e = e' := Nat.pow_right_injective (le_refl 2) hq'
    subst hee
    set kb : ↥Xb := ⟨yb, hybX⟩ with hkb
    have hkb1 : kb ≠ 1 := by
      intro h
      have h1 : yb = 1 := congrArg Subtype.val h
      rw [hyb, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hd1 : orderOf (⟨y, hyGv⟩ : ↥Gv) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy3))
      have hd2 : orderOf (⟨⟨y, hyGv⟩, h1⟩ : ↥(CFSG.pPrimeCore 3 ↥Gv)) ∣
          Nat.card ↥(CFSG.pPrimeCore 3 ↥Gv) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hd2
      have hcop := Nat.Coprime.coprime_dvd_right hd2 (CFSG.pPrimeCore_coprime_card (p := 3))
      have h1' : orderOf (⟨y, hyGv⟩ : ↥Gv) = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hd1
      have hy1 : y = 1 := by
        have := congrArg Subtype.val (orderOf_eq_one_iff.mp h1')
        simpa using this
      apply hyz
      rw [hy1]
      simp
    have hkb3 : orderOf kb = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa [hkb] using hyb3)) hkb1
    have hkbL : kb ∈ L₀ := h3L₀ kb hkb3
    set KsX : Subgroup ↥Xb := Ks.subgroupOf Xb with hKsXdef
    let eK : ↥KsX ≃* ↥Ks := Subgroup.subgroupOfEquivOfLe hKsX
    have hcomm : ∀ x y : ↥Xb ⧸ L₀, x * y = y * x := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic (↥Xb ⧸ L₀) := isCyclic_of_prime_card (p := 3) hcard3
      exact fun x y => (IsCyclic.isMulCommutative (α := ↥Xb ⧸ L₀)).is_comm.comm x y
    let f : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥Xb ⧸ L₀ :=
      (QuotientGroup.mk' L₀).comp (KsX.subtype.comp (eK.symm.toMonoidHom.comp Θ.symm.toMonoidHom))
    have hfker : f.ker = ⊤ := by
      have hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := Group.isPerfect_def.mp hq.1
      rw [eq_top_iff, ← hperf, commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have hKsL : KsX ≤ L₀ := by
      intro κ hκ
      have h1 : f (Θ (eK ⟨κ, hκ⟩)) = 1 := by
        rw [← MonoidHom.mem_ker, hfker]
        exact Subgroup.mem_top _
      have h2 : f (Θ (eK ⟨κ, hκ⟩)) = QuotientGroup.mk' L₀ κ := by
        show QuotientGroup.mk' L₀ ((eK.symm (Θ.symm (Θ (eK ⟨κ, hκ⟩))) : ↥KsX) : ↥Xb) = _
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hcardKs : Nat.card ↥L₀ ≤ Nat.card ↥KsX := by
      rw [Nat.card_congr eK.toEquiv, ConfAB.card_eq_of_isPSLEps3 hPSL hPSL₀]
    have heq : KsX = L₀ := Subgroup.eq_of_le_of_card_ge hKsL hcardKs
    have hybKs : yb ∈ Ks := by
      have : kb ∈ KsX := heq ▸ hkbL
      exact this
    refine ⟨Θ ⟨yb, hybKs⟩, ?_⟩
    ext x
    obtain ⟨κ, rfl⟩ := Θ.surjective x
    rw [← hΘc y hyGv hyN κ, MulAut.conj_apply]
    have e : (⟨π₃ ⟨y, hyGv⟩ * κ * (π₃ ⟨y, hyGv⟩)⁻¹, hKsn.conj_mem _ κ.2 _⟩ : ↥Ks) =
        ⟨yb, hybKs⟩ * κ * (⟨yb, hybKs⟩ : ↥Ks)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]

end Setting

end CFSG.Quasithin.H13.A5
