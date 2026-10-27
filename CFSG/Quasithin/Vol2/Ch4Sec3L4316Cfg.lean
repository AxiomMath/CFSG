module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Lab2
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316W
public import CFSG.Quasithin.Background.OperatorJordanHolderJH2
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Par
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Pgl

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat CFSG.Quasithin.OperatorJH
open CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
open scoped MatrixGroups Matrix Pointwise

variable {G : Type} [Group G] [Finite G]

namespace L4316

theorem le_normalizer_of_comm {A B C : Subgroup G} (hBC : B ≤ C) (hCA : C ≤ A)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) :
    A ≤ Subgroup.normalizer (C : Set G) := fun a ha =>
  CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun c hc => by
    have h1 := hBC (hcomm a ha c (hCA hc))
    have e : a * c * a⁻¹ = (a * c * a⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact C.mul_mem h1 hc

end L4316

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem R₂_le_normalizer_pCoreOf_KZ :
    R₂ ≤ Subgroup.normalizer ((pCoreOf 2 KZ : Subgroup G) : Set G) :=
  (s.R₂_le_G₀.trans s.G₀_le_normalizer_KZ).trans (normalizer_le_normalizer_pCoreOf 2 KZ)

theorem Γ_le_normalizer_pCoreOf_KZ :
    KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer ((pCoreOf 2 KZ : Subgroup G) : Set G) :=
  s.Γ_le_normalizer_KZ.trans (normalizer_le_normalizer_pCoreOf 2 KZ)

theorem star_of (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) {A B : Subgroup G}
    (hAN : A ≤ pCoreOf 2 KZ)
    (hΓA : KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) :
    ∀ C₁ C₂ : Subgroup G, B ≤ C₁ → C₁ < C₂ → C₂ ≤ A →
      K₂ ≤ Subgroup.normalizer (C₁ : Set G) → K₂ ≤ Subgroup.normalizer (C₂ : Set G) →
      (∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → K₂ ≤ Subgroup.normalizer (J : Set G) →
        J = C₁ ∨ J = C₂) →
      (∃ l ∈ K₂, ∃ c ∈ C₂, l * c * l⁻¹ * c⁻¹ ∉ C₁) →
      ∃ N' : Subgroup ↥K₂, IsNaturalSection K₂ C₂ C₁ N' (StatedSL 2 F) := by
  intro C₁ C₂ hBC₁ hlt hC₂A hK₁ hK₂ hirr hnc
  have hK₂Γ : K₂ ≤ KZ ⊔ Subgroup.zpowers y := s.K₂_le_KZ.trans le_sup_left
  obtain ⟨l, hl, -⟩ := s.exists_labSeries_R₂ h135 hR hC h37 h38 h39 hm 1
  obtain ⟨lK, hlK⟩ := L4316.IsLabSeries.exists_toK hl le_sup_left le_rfl s.leviS_surjective
  have hJH := fun C D l hl => operatorJHNatEig_holds G K₂ K₂ 1 2 F s.leviS le_rfl K₂.one_mem
    le_rfl s.leviS_surjective C D l hl
  obtain ⟨l₁, -, hl₁, -, -⟩ := (hJH ⊥ R₂ lK hlK).2 (pCoreOf 2 KZ) bot_le s.pCoreOf_KZ_le
    (L4316.le_normalizer_bot _) s.R₂_le_normalizer_pCoreOf_KZ
    (hK₂Γ.trans s.Γ_le_normalizer_pCoreOf_KZ)
  obtain ⟨l₂, -, hl₂, -, -⟩ := (hJH ⊥ (pCoreOf 2 KZ) l₁ hl₁).2 A bot_le hAN
    (L4316.le_normalizer_bot _) (((pCoreOf_le 2 KZ).trans le_sup_left).trans hΓA)
    (hK₂Γ.trans hΓA)
  obtain ⟨-, l₃, -, hl₃, -⟩ := (hJH ⊥ A l₂ hl₂).2 C₁ bot_le (hlt.le.trans hC₂A)
    (L4316.le_normalizer_bot _) (L4316.le_normalizer_of_comm hBC₁ (hlt.le.trans hC₂A) hcomm) hK₁
  obtain ⟨l₄, -, hl₄, -, -⟩ := (hJH C₁ A l₃ hl₃).2 C₂ hlt.le hC₂A
    ((hC₂A.trans (L4316.le_normalizer_of_comm hBC₁ (hlt.le.trans hC₂A) hcomm)))
    (L4316.le_normalizer_of_comm (hBC₁.trans hlt.le) hC₂A hcomm) hK₂
  obtain ⟨e, he⟩ := L4316.IsLabSeries.exists_factor hl₄ hlt hirr
  obtain ⟨-, -, -, -, -, hlab⟩ := he
  cases e with
  | none =>
    exfalso
    obtain ⟨l', hl', c, hc, hlc⟩ := hnc
    exact hlc (hlab l' hl' c hc)
  | some a =>
    obtain ⟨βC, hβs, hβk, hβK, -⟩ := hlab
    refine ⟨s.leviS.ker, hK₂, s.leviS, s.leviS_surjective, rfl, βC, hβs, ?_, hβK⟩
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk c

variable {α' : ↥(KZ ⊔ Subgroup.zpowers y) →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
  {P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))}
  {α₀' : ↥(perfectCore P) →* ↥(StatedSL 2 F)}

theorem map_K₂_ne_bot (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ) :
    (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' ≠ ⊥ := by
  intro h
  apply s.not_K₂_le_pCoreOf_KZ
  intro k hk
  have hkΓ : k ∈ KZ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left (s.K₂_le_KZ hk)
  have h1 : α' ⟨k, hkΓ⟩ ∈ (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' :=
    ⟨⟨k, hkΓ⟩, hk, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (hα'k _).mp h1

theorem natEig_O₂ (hm : m = 2) (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ)
    (hPK₂ : (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' = perfectCore P)
    (hcompat : ∀ (l : ↥K₂) (γ : ↥(KZ ⊔ Subgroup.zpowers y)) (p : ↥(perfectCore P)),
      (γ : G) = l → (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = α' γ →
        s.leviS l = α₀' p)
    {γx : ↥(KZ ⊔ Subgroup.zpowers y)} {μ' : F}
    (hNE : IsNatEigSection (perfectCore P) (α' γx) α₀' ⊥ (pCoreOf 2 (perfectCore P)) μ') :
    IsNatEigSection K₂ (γx : G) s.leviS (pCoreOf 2 KZ) (pCoreOf 2 KZ ⊔ pCoreOf 2 K₂) μ' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, s.card_F, hm]; norm_num
  have hK₂Γ : K₂ ≤ (KZ ⊔ Subgroup.zpowers y) := s.K₂_le_KZ.trans le_sup_left
  have hEΓ : pCoreOf 2 KZ ⊔ pCoreOf 2 K₂ ≤ (KZ ⊔ Subgroup.zpowers y) :=
    _root_.sup_le ((pCoreOf_le 2 KZ).trans le_sup_left) ((pCoreOf_le 2 K₂).trans hK₂Γ)
  set O := pCoreOf 2 (perfectCore P) with hO
  have hperf : ⁅(K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α',
      (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α'⁆ =
      (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' := by
    rw [← Subgroup.map_commutator, L4316.subgroupOf_perfect hK₂Γ s.K₂_perfect]
  have hne := s.map_K₂_ne_bot hα'k
  have hOle : ((pCoreOf 2 K₂).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' ≤ O := by
    rw [hO, ← hPK₂]
    exact S12.map_pCoreOf_le α' hK₂Γ
  have hEP : ∀ e : ↥(pCoreOf 2 KZ ⊔ pCoreOf 2 K₂), α' ⟨e, hEΓ e.2⟩ ∈ O := by
    intro e
    set T := (O.comap α').map (KZ ⊔ Subgroup.zpowers y).subtype with hT
    have h1 : pCoreOf 2 KZ ⊔ pCoreOf 2 K₂ ≤ T := by
      refine _root_.sup_le (fun k hk => ⟨⟨k, (pCoreOf_le 2 KZ).trans le_sup_left hk⟩, ?_, rfl⟩)
        (fun k hk => ⟨⟨k, (pCoreOf_le 2 K₂).trans hK₂Γ hk⟩, hOle ⟨_, hk, rfl⟩, rfl⟩)
      show α' _ ∈ O
      rw [(hα'k _).mpr hk]
      exact O.one_mem
    obtain ⟨γ, hγ, hγe⟩ := h1 e.2
    have : (⟨e, hEΓ e.2⟩ : ↥(KZ ⊔ Subgroup.zpowers y)) = γ := Subtype.ext hγe.symm
    rw [this]
    exact hγ
  set φ : ↥(pCoreOf 2 KZ ⊔ pCoreOf 2 K₂) →* ↥O :=
    (α'.comp (Subgroup.inclusion hEΓ)).codRestrict O hEP with hφ
  obtain ⟨βP, hβPs, hβPk, hβPK, hβPx⟩ := hNE
  refine ⟨βP.comp φ, fun w => ?_, fun e => ?_, fun k e e' he => ?_, fun e e' he => ?_⟩
  · obtain ⟨c, hc⟩ := hβPs w
    have hcO : (c : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ∈
        ((pCoreOf 2 K₂).subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' := by
      have h1 :=
        S12.pCoreOf_le_map hF hK₂Γ α' hperf hne s.leviS s.leviS_surjective s.leviS_ker
      have hc2 : (c : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ∈
          pCoreOf 2 ((K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α') := by
        rw [hPK₂]
        exact c.2
      exact h1 hc2
    obtain ⟨γ, hγ, hγc⟩ := hcO
    have hγE : (γ : G) ∈ pCoreOf 2 KZ ⊔ pCoreOf 2 K₂ :=
      Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hγ)
    refine ⟨⟨γ, hγE⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    convert hc
    exact Subtype.ext hγc
  · rw [MonoidHom.comp_apply, hβPk, Subgroup.mem_bot]
    change α' ⟨e, hEΓ e.2⟩ = 1 ↔ _
    exact hα'k _
  · have hkΓ : (k : G) ∈ (KZ ⊔ Subgroup.zpowers y) := hK₂Γ k.2
    have hkP : α' ⟨k, hkΓ⟩ ∈ perfectCore P := hPK₂ ▸ ⟨⟨k, hkΓ⟩, k.2, rfl⟩
    have h1 := hβPK ⟨_, hkP⟩ (φ e) (φ e') (by
      change α' ⟨e', hEΓ e'.2⟩ = α' ⟨k, hkΓ⟩ * α' ⟨e, hEΓ e.2⟩ * (α' ⟨k, hkΓ⟩)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1,
      ← hcompat k ⟨k, hkΓ⟩ ⟨_, hkP⟩ rfl rfl]
  · have h1 := hβPx (φ e) (φ e') (by
      change α' ⟨e', hEΓ e'.2⟩ = α' γx * α' ⟨e, hEΓ e.2⟩ * (α' γx)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1]

theorem exists_labSeries_O₂_R₂ (hm : m = 2) (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ)
    (hPK₂ : (K₂.subgroupOf (KZ ⊔ Subgroup.zpowers y)).map α' = perfectCore P)
    (hcompat : ∀ (l : ↥K₂) (γ : ↥(KZ ⊔ Subgroup.zpowers y)) (p : ↥(perfectCore P)),
      (γ : G) = l → (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = α' γ →
        s.leviS l = α₀' p)
    {γx : ↥(KZ ⊔ Subgroup.zpowers y)} {μ' : F}
    (hNE : IsNatEigSection (perfectCore P) (α' γx) α₀' ⊥ (pCoreOf 2 (perfectCore P)) μ') :
    ∃ l : List (Subgroup G × Option F),
      IsLabSeries (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G) s.leviS (pCoreOf 2 KZ) l R₂ ∧
        labMultiset l = ({μ'} : Multiset F) := by
  have hE := s.natEig_O₂ hm hα'k hPK₂ hcompat hNE
  set E := pCoreOf 2 KZ ⊔ pCoreOf 2 K₂ with hEdef
  have hYΓ : K₂ ⊔ Subgroup.zpowers y ≤ KZ ⊔ Subgroup.zpowers y :=
    _root_.sup_le (s.K₂_le_KZ.trans le_sup_left) le_sup_right
  have hYO : K₂ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer ((pCoreOf 2 KZ : Subgroup G) : Set G) :=
    hYΓ.trans s.Γ_le_normalizer_pCoreOf_KZ
  have hYO₂ : K₂ ⊔ Subgroup.zpowers y ≤
      Subgroup.normalizer ((pCoreOf 2 K₂ : Subgroup G) : Set G) :=
    _root_.sup_le (le_normalizer_pCoreOf 2 K₂)
      (s.Y_le_normalizer_K₂.trans (normalizer_le_normalizer_pCoreOf 2 K₂))
  have hYE : K₂ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set G) := fun g hg =>
    mem_normalizer_sup_of (hYO hg) (hYO₂ hg)
  have hEN : E ≤ Subgroup.normalizer ((pCoreOf 2 KZ : Subgroup G) : Set G) :=
    (_root_.sup_le (pCoreOf_le 2 KZ) ((pCoreOf_le 2 K₂).trans s.K₂_le_KZ)).trans
      (le_normalizer_pCoreOf 2 KZ)
  have hlt := L4316.lt_of_natEig hE le_sup_left le_rfl s.leviS_surjective
    (le_sup_left.trans hYE)
  have hf := L4316.isLabFactor_of_natEig hE hlt hEN hYO hYE le_sup_left le_rfl
    s.leviS_surjective
  have hER : E ≤ R₂ := _root_.sup_le s.pCoreOf_KZ_le s.pCoreOf_K₂_le_R₂
  have hRE : R₂ ≤ Subgroup.normalizer (E : Set G) := fun r hr =>
    mem_normalizer_sup_of (s.R₂_le_normalizer_pCoreOf_KZ hr)
      (normalizer_le_normalizer_pCoreOf 2 K₂ (s.R₂_le_normalizer_K₂ hr))
  obtain ⟨lc, hlc, hlcn⟩ := L4316.exists_isLabSeries_central (Y := K₂ ⊔ Subgroup.zpowers y)
    (x := (γx : G)) (α₀ := s.leviS) hER hRE hYE s.le_normalizer_R₂' (fun k hk r hr => by
      refine Subgroup.mem_sup_right (s.R₂_inf_K₂_le ⟨?_, ?_⟩)
      · have h1 : k * r * k⁻¹ ∈ R₂ :=
          (Subgroup.mem_normalizer_iff.mp (le_sup_left.trans s.le_normalizer_R₂ hk) r).mp hr
        exact R₂.mul_mem h1 (R₂.inv_mem hr)
      · have h1 : r * k⁻¹ * r⁻¹ ∈ K₂ :=
          (Subgroup.mem_normalizer_iff.mp (s.R₂_le_normalizer_K₂ hr) _).mp (K₂.inv_mem hk)
        have e : k * r * k⁻¹ * r⁻¹ = k * (r * k⁻¹ * r⁻¹) := by group
        rw [e]
        exact K₂.mul_mem hk h1)
  refine ⟨(E, some μ') :: lc, ⟨hf, hlc⟩, ?_⟩
  rw [labMultiset_cons, labMultiset_eq_zero_of_forall hlcn, add_zero]
  rfl

end Setting4315

theorem step43L34_of (hB414 : LemmaB414Corrected) (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Step43L34 := by
  intro G _ _ T M L n I H K t m F _ _ α β W' ZS K₂ R₂ μ y KZ s0 hKZ hGZ hK₂ hKZC hF4 hQL hN hO2
    hR₂ hA
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ :=
    ⟨s0, hKZ, hGZ, hK₂, hKZC, hN, hO2, hR₂⟩
  have hm : m = 2 := by
    have h1 := s0.card_F
    rw [hF4] at h1
    have h2 : (2 : ℕ) ^ m = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective le_rfl h2
  have : CharP F 2 := s.charP
  have hF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF4]
  have hSK : IsSimpleGroup
      ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))) := by
    obtain ⟨s', q, -, hpslq, -⟩ := hA
    exact L436.isSimpleGroup_of_isPSLEps3q hpslq
  have hZ := s.center_modO2_eq_bot h135 hR hC h36 h37 h38 h39 hSK
  obtain ⟨α', hα's, hα'k⟩ := s.exists_alpha_of h135 hR hC h36 h37 h38 h39 hm hA hQL
  obtain ⟨A, B, hAN, hBA, hΓA, hΓB, hsq, hcomm, hirr, hker, -⟩ :=
    s.exists_W h135 hR hC h36 h37 h38 h39 hm hZ hα's hα'k
  obtain ⟨P, hPmax, hPK₂, hPX, hXcard, hXcent⟩ :=
    s.exists_P h135 hR hC h36 h37 h38 h39 hm hZ hQL hα'k
  have hstar := s.star_of (F := F) h135 hR hC h37 h38 h39 hm hAN hΓA hcomm
  have hK₂Γ : K₂ ≤ KZ ⊔ Subgroup.zpowers y := s.K₂_le_KZ.trans le_sup_left
  have hYΓ : K₂ ⊔ Subgroup.zpowers y ≤ KZ ⊔ Subgroup.zpowers y := _root_.sup_le hK₂Γ le_sup_right
  obtain ⟨⟨k, hk3, hk⟩, hrest⟩ := hB414 G (KZ ⊔ Subgroup.zpowers y) A B K₂ (Subgroup.zpowers y) F
    hF4 hΓA hΓB hBA hsq hcomm hirr hK₂Γ le_sup_right α' hα's hker P hPmax hPK₂ hPX hXcard
    hXcent hstar
  obtain ⟨-, -, tw, -, -, -, hlab⟩ := hrest k hk3 hk
  have hne : perfectCore P ≠ ⊥ := by
    rw [← hPK₂]
    exact s.map_K₂_ne_bot hα'k
  obtain ⟨α₀', hα₀'s, hα₀'k, hcompat⟩ := S12.exists_levi hF hK₂Γ α' hPK₂ (perfectCore_perfect P)
    hne s.leviS s.leviS_surjective s.leviS_ker
  have hlabels : ∀ γx : ↥(KZ ⊔ Subgroup.zpowers y), (γx : G) ∈ Subgroup.zpowers y →
      α' γx ≠ 1 → ∃ (U : Subgroup G) (ω₀ μ' : F), ω₀ ≠ 1 ∧ ω₀ ^ 3 = 1 ∧
        IsNatEigSection (perfectCore P) (α' γx) α₀' ⊥ (pCoreOf 2 (perfectCore P)) μ' ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G)
          s.leviS ⊥ l R₂ ∧ labMultiset l = ({ω₀, ω₀⁻¹, ω₀⁻¹, 1} : Multiset F)) ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G)
          s.leviS ⊥ l B ∧ ∀ q ∈ l, q.2 = none) ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G)
          s.leviS A l (pCoreOf 2 KZ) ∧ ∀ q ∈ l, q.2 = none) ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G)
          s.leviS (pCoreOf 2 KZ) l R₂ ∧ labMultiset l = ({μ'} : Multiset F)) ∧
        IsLabFactor (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G) s.leviS ZS U (some ω₀) ∧
        U ≤ pCoreOf 2 K₂ ∧ ⁅U, pCoreOf 2 K₂⁆ ≤ ZS ∧ (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧
        K₂ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (U : Set G) ∧
        pCoreOf 2 KZ ≤ Subgroup.normalizer (U : Set G) := by
    intro γx hγx hγx1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hγx
    have hμ3 : μ ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, s0.μ_order, hm]
      norm_num
    have hω1 : ((μ ^ j : Fˣ) : F) ≠ 1 := by
      intro h1
      apply hγx1
      have h2 : μ ^ j = 1 := Units.ext h1
      have h3 : (orderOf μ : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr h2
      have h4 : y ^ j = 1 := by
        apply orderOf_dvd_iff_zpow_eq_one.mp
        rw [s.orderOf_y, ← s0.μ_order]
        exact h3
      have h5 : γx = 1 := Subtype.ext (by rw [← hj, h4]; rfl)
      rw [h5, map_one]
    have hω3 : ((μ ^ j : Fˣ) : F) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hμ3, one_zpow, Units.val_one]
    obtain ⟨μ', hNE, lW, hlW, hlWm⟩ := hlab α₀' hα₀'s hα₀'k s.leviS hcompat γx hγx hγx1
    obtain ⟨lR, hlR, hlRm⟩ := s.exists_labSeries_R₂ h135 hR hC h37 h38 h39 hm j
    rw [hj] at hlR
    obtain ⟨lO, hlO, hlOm⟩ := s.exists_labSeries_O₂_R₂ hm hα'k hPK₂ hcompat hNE
    have hJH := fun C D l hl => operatorJHNatEig_holds G (K₂ ⊔ Subgroup.zpowers y) K₂ (γx : G) 2
      F s.leviS le_sup_left (Subgroup.mem_sup_right hγx) le_rfl s.leviS_surjective C D l hl
    have hYO : K₂ ⊔ Subgroup.zpowers y ≤
        Subgroup.normalizer ((pCoreOf 2 KZ : Subgroup G) : Set G) :=
      hYΓ.trans s.Γ_le_normalizer_pCoreOf_KZ
    obtain ⟨l₁, l₂, hl₁, hl₂, hm₁₂⟩ := (hJH ⊥ R₂ lR hlR).2 (pCoreOf 2 KZ) bot_le
      s.pCoreOf_KZ_le (L4316.le_normalizer_bot _) s.R₂_le_normalizer_pCoreOf_KZ hYO
    obtain ⟨l₃, l₄, hl₃, hl₄, hm₃₄⟩ := (hJH ⊥ (pCoreOf 2 KZ) l₁ hl₁).2 A bot_le hAN
      (L4316.le_normalizer_bot _) (((pCoreOf_le 2 KZ).trans le_sup_left).trans hΓA)
      (hYΓ.trans hΓA)
    obtain ⟨l₅, l₆, hl₅, hl₆, hm₅₆⟩ := (hJH ⊥ A l₃ hl₃).2 B bot_le hBA.le
      (L4316.le_normalizer_bot _) (((hAN.trans (pCoreOf_le 2 KZ)).trans le_sup_left).trans hΓB)
      (hYΓ.trans hΓB)
    have hm₂ : labMultiset l₂ = ({μ'} : Multiset F) := ((hJH _ _ lO hlO).1 l₂ hl₂).trans hlOm
    have hm₆ := ((hJH _ _ lW hlW).1 l₆ hl₆).trans hlWm
    have hcard : Multiset.card (labMultiset l₅) + Multiset.card (labMultiset l₄) = 0 := by
      have h1 := congrArg Multiset.card hlRm
      rw [← hm₁₂, ← hm₃₄, ← hm₅₆, hm₂, hm₆] at h1
      simp only [Multiset.card_add, Multiset.insert_eq_cons, Multiset.card_cons,
        Multiset.card_singleton] at h1
      omega
    have h5 : labMultiset l₅ = 0 := Multiset.card_eq_zero.mp (by omega)
    have h4 : labMultiset l₄ = 0 := Multiset.card_eq_zero.mp (by omega)
    have hfU := s.isLabFactor_U hm j
    rw [hj] at hfU
    refine ⟨u4311 I K, ((μ ^ j : Fˣ) : F), μ', hω1, hω3, hNE, ⟨lR, hlR, hlRm⟩,
      ⟨l₅, hl₅, L4316.forall_eq_none_of_labMultiset_eq_zero h5⟩,
      ⟨l₄, hl₄, L4316.forall_eq_none_of_labMultiset_eq_zero h4⟩, ⟨lO, hlO, hlOm⟩, hfU,
      s.U_le_pCoreOf_K₂ h135 hR hC h37 h38 h39, s.commutator_U_le_ZS,
      fun a ha b hb => L4316.u4311_comm ha hb, s.le_normalizer_U, s.pCoreOf_KZ_le_normalizer_U⟩
  refine ⟨KZ ⊔ Subgroup.zpowers y, A, B, α', P,
    ⟨s0.sk, s0.charTwo, s0.c41, s0.c3, s0.c134, s0.cent, hF4, s0.ZS_eq, s0.K₂_eq, s0.R₂_eq, hKZ,
      hGZ, hK₂, hQL, s.pCoreOf_KZ_le, ?_, Subgroup.zpowers_le.mpr s0.y_mem,
      fun x hx k hk => s.comm_mem_pCoreOf_K hm hx hk, s.Y_le_normalizer_ZS,
      s.Y_le_normalizer_K₂, rfl, hAN, hBA, hΓA, hΓB, hsq, hcomm, hirr, hα's, hker,
      fun γ h => (hα'k γ).mp h, hPmax, hPK₂, hPX, hXcard, hXcent, hstar,
      fun J hJ hJn => s.D_irred h135 hR hC h37 h38 h39 hm J hJ hJn,
      fun d hd hfix => s.eq_one_of_fixed_D h135 hR hC h37 h38 h39 hm hd hfix,
      fun r hr k hk => s.commutator_mem_D hr hk, hKZC,
      ⟨α₀', s.leviS, hα₀'s, hα₀'k, hcompat, hlabels⟩⟩⟩
  rw [s.card_Y, hm]
  norm_num

end CFSG.Quasithin.H13.Ch4
