module

public import CFSG.Quasithin.Vol2.Ch9Sec3Conj
public import CFSG.Quasithin.Vol2.Ch9Sec3Borel
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522Bot
public import CFSG.Quasithin.Vol2.Ch9Sec3Cart

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix
open scoped Pointwise

section General

variable {G : Type} [Group G]

@[expose] def cenMod (T R B : Subgroup G) : Subgroup G where
  carrier := {s | s ∈ T ⊓ Subgroup.normalizer (R : Set G) ∧
    ∀ b ∈ B ⊓ Subgroup.normalizer (R : Set G), s * b * s⁻¹ * b⁻¹ ∈ R}
  mul_mem' := by
    rintro s s' ⟨hs, hsB⟩ ⟨hs', hs'B⟩
    refine ⟨mul_mem hs hs', fun b hb => ?_⟩
    have h3 : s * (s' * b * s'⁻¹ * b⁻¹) * s⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hs.2 _).mp (hs'B b hb)
    have e : s * s' * b * (s * s')⁻¹ * b⁻¹ =
        (s * (s' * b * s'⁻¹ * b⁻¹) * s⁻¹) * (s * b * s⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem h3 (hsB b hb)
  one_mem' := ⟨one_mem _, fun b _ => by simp⟩
  inv_mem' := by
    rintro s ⟨hs, hsB⟩
    refine ⟨inv_mem hs, fun b hb => ?_⟩
    have h1 := hsB b⁻¹ (inv_mem hb)
    have h2 : b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hb.2 _).mp h1
    have h3 : s⁻¹ * (b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹) * s⁻¹⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hs.2) _).mp h2
    have e : s⁻¹ * b * s⁻¹⁻¹ * b⁻¹ =
        s⁻¹ * (b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹) * s⁻¹⁻¹ := by group
    rw [e]
    exact h3

theorem cenMod_le (T R B : Subgroup G) : cenMod T R B ≤ T := fun _ hs => hs.1.1

theorem le_cenMod {T R B : Subgroup G} (hRT : R ≤ T) : R ≤ cenMod T R B := by
  intro r hr
  refine ⟨⟨hRT hr, Subgroup.le_normalizer hr⟩, fun b hb => ?_⟩
  have h1 : b * r⁻¹ * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hb.2 _).mp (inv_mem hr)
  have e : r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) := by group
  rw [e]
  exact mul_mem hr h1

theorem mem_normalizer_of_conj_le [Finite G] {H : Subgroup G} {x : G}
    (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    show (MulAut.conj x) y ∈ H
    rw [MulAut.conj_apply]
    exact h y hy
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge)

theorem le_normalizer_cenMod_of_le [Finite G] {T R B : Subgroup G}
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hTB : ∀ u ∈ T, ∀ b ∈ B, ∃ b₁ ∈ B, u⁻¹ * b * u * b₁⁻¹ ∈ R) :
    T ≤ Subgroup.normalizer (cenMod T R B : Set G) := by
  intro u hu
  refine mem_normalizer_of_conj_le fun s hs => ?_
  obtain ⟨⟨hsT, hsN⟩, hsB⟩ := hs
  refine ⟨⟨T.mul_mem (T.mul_mem hu hsT) (T.inv_mem hu),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTR hu) hsN) (Subgroup.inv_mem _ (hTR hu))⟩,
    fun b hb => ?_⟩
  obtain ⟨b₁, hb₁, hr₁⟩ := hTB u hu b hb.1
  set r₁ := u⁻¹ * b * u * b₁⁻¹ with hr₁def
  have hb'' : u⁻¹ * b * u = r₁ * b₁ := by rw [hr₁def]; group
  have h1 : s * r₁ * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hsN _).mp hr₁
  have h2 := hsB b₁ ⟨hb₁, hBR hb₁⟩
  have h3 : (s * r₁ * s⁻¹) * (s * b₁ * s⁻¹ * b₁⁻¹) * r₁⁻¹ ∈ R :=
    mul_mem (mul_mem h1 h2) (inv_mem hr₁)
  have h4 : u * ((s * r₁ * s⁻¹) * (s * b₁ * s⁻¹ * b₁⁻¹) * r₁⁻¹) * u⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hTR hu) _).mp h3
  have e : u * s * u⁻¹ * b * (u * s * u⁻¹)⁻¹ * b⁻¹ =
      u * ((s * r₁ * s⁻¹) * (s * b₁ * s⁻¹ * b₁⁻¹) * r₁⁻¹) * u⁻¹ := by
    have e1 : b = u * (r₁ * b₁) * u⁻¹ := by rw [← hb'']; group
    calc u * s * u⁻¹ * b * (u * s * u⁻¹)⁻¹ * b⁻¹
        = u * s * u⁻¹ * (u * (r₁ * b₁) * u⁻¹) * (u * s * u⁻¹)⁻¹ *
            (u * (r₁ * b₁) * u⁻¹)⁻¹ := by rw [← e1]
      _ = _ := by group
  rw [e]
  exact h4

theorem le_normalizer_cenMod_of_comm [Finite G] {T R B : Subgroup G} (hRT : R ≤ T)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    B ≤ Subgroup.normalizer (cenMod T R B : Set G) := by
  intro b' hb'
  refine mem_normalizer_of_conj_le fun s hs => ?_
  obtain ⟨⟨hsT, hsN⟩, hsB⟩ := hs
  have hc' : s * b' * s⁻¹ * b'⁻¹ ∈ R := hsB b' ⟨hb', hBR hb'⟩
  refine ⟨⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBR hb') hsN)
    (Subgroup.inv_mem _ (hBR hb'))⟩, fun b hb => ?_⟩
  · have e : b' * s * b'⁻¹ = (s * b' * s⁻¹ * b'⁻¹)⁻¹ * s := by group
    rw [e]
    exact T.mul_mem (hRT (inv_mem hc')) hsT
  · have h1 := hsB b hb
    have h2 : b' * (s * b * s⁻¹ * b⁻¹) * b'⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hBR hb') _).mp h1
    have hbb : b'⁻¹ * b * b' = b := by
      rw [mul_assoc, hBab b hb.1 b' hb', ← mul_assoc, inv_mul_cancel, one_mul]
    have e : b' * s * b'⁻¹ * b * (b' * s * b'⁻¹)⁻¹ * b⁻¹ = b' * (s * b * s⁻¹ * b⁻¹) * b'⁻¹ := by
      calc b' * s * b'⁻¹ * b * (b' * s * b'⁻¹)⁻¹ * b⁻¹
          = b' * s * (b'⁻¹ * b * b') * s⁻¹ * b'⁻¹ * b⁻¹ := by group
        _ = b' * s * b * s⁻¹ * b'⁻¹ * b⁻¹ := by rw [hbb]
        _ = b' * (s * b * s⁻¹ * b⁻¹) * (b * b'⁻¹ * b⁻¹) := by group
        _ = b' * (s * b * s⁻¹ * b⁻¹) * b'⁻¹ := by
          rw [show b * b'⁻¹ * b⁻¹ = b'⁻¹ by
            rw [← hBab b'⁻¹ (B.inv_mem hb') b hb.1]
            group]
    rw [e]
    exact h2

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

omit [Finite G] in
theorem r0_le_T : (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤ T :=
  sup_le inf_le_left inf_le_left

include S in
theorem isPGroup_r0 :
    IsPGroup 2 ↥((T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G))) :=
  S.hyp.fsu.sylow.1.to_le r0_le_T

include S in
theorem T_le_normalizer_r0 :
    T ≤ Subgroup.normalizer (((T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :
      Subgroup G) : Set G) :=
  le_normalizer_sup_of_le_of_le
    (fun _ ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, Setup.T_le_normalizer_L0 ht⟩)
    (fun _ ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, mem_normalizer_centralizer (S.T_le_normalizer_V ht)⟩)

include S in
theorem N0_le_normalizer_r0 :
    fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (((T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :
        Subgroup G) : Set G) := by
  refine le_normalizer_sup_of_le_of_le inf_le_right ?_
  rw [← S.hQ]
  exact (inf_le_left.trans le_sup_left).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (fsuL0 T L ⊔ T))

omit [Finite G] in
theorem r0_le_centralizer_V1 :
    (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤
      Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  refine sup_le (fun s hs => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    (inf_le_right.trans (Subgroup.centralizer_le fun v hv => hv.1))
  exact (Subgroup.mem_centralizer_iff.mp hv.2 s hs).symm

include S in
theorem exists_mul_mem_r0_of_mem_B {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G))) :
    ∀ u ∈ T, ∀ b ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G),
      ∃ b₁ ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G),
        u⁻¹ * b * u * b₁⁻¹ ∈ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  intro u hu b hb
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hN₀eq : N₀ = P₀ ⊔ D :=
    le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall S.isSylowTwoOf_T_inf_L0_normalizer hD)
      (sup_le S.isSylowTwoOf_T_inf_L0_normalizer.1 hD.1)
  have hDN : D ≤ Subgroup.normalizer (P₀ : Set G) := hD.1.trans inf_le_right
  have hset2 : (N₀ : Set G) = (P₀ : Set G) * (D : Set G) := by
    rw [hN₀eq]
    exact Subgroup.coe_mul_of_right_le_normalizer_left P₀ D hDN
  have hconj : u⁻¹ * b * u⁻¹⁻¹ ∈ (N₀ : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_N0 (T.inv_mem hu)) b).mp (hD.1 hb.1)
  rw [hset2] at hconj
  obtain ⟨s, hs, d, hd, hsd⟩ := hconj
  have hsd' : s * d = u⁻¹ * b * u := by simpa using hsd
  have hbV : u⁻¹ * b * u⁻¹⁻¹ ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer
      (S.T_le_normalizer_V1 (T.inv_mem hu))) b).mp hb.2
  have hsV := r0_le_centralizer_V1 (T := T) (L := L) (I := I) (Subgroup.mem_sup_left hs)
  have hdV : d ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    have e : d = s⁻¹ * (u⁻¹ * b * u⁻¹⁻¹) := by rw [inv_inv, ← hsd']; group
    rw [e]
    exact mul_mem (inv_mem hsV) hbV
  refine ⟨d, ⟨hd, hdV⟩, ?_⟩
  have e : u⁻¹ * b * u * d⁻¹ = s := by rw [← hsd']; group
  rw [e]
  exact Subgroup.mem_sup_left hs

theorem mem_normalizer_sup_zpowers {R : Subgroup G} {g x : G}
    (hxR : x ∈ Subgroup.normalizer (R : Set G)) (hxg : x * g * x⁻¹ ∈ R ⊔ Subgroup.zpowers g) :
    x ∈ Subgroup.normalizer ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := by
  have hle : (R ⊔ Subgroup.zpowers g).map (MulAut.conj x).toMonoidHom ≤
      R ⊔ Subgroup.zpowers g := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [show R.map (MulAut.conj x).toMonoidHom = R from
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp hxR)]
      exact le_sup_left
    · rw [MonoidHom.map_zpowers]
      refine (Subgroup.zpowers_le).mpr ?_
      simpa [MulAut.conj_apply] using hxg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge)

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem ne_one_of_forms {t : G} (ht : t ∈ T) {A B A' B' : GL (Fin 2) K} {τ τ' : K ≃+* K}
    (h : bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM τ ∨
      bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM)
    (h' : bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A' B' * Om4.frM τ' ∨
      bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A' B' * Om4.frM τ' * Om4.trM)
    (hτ : τ ≠ 1) : τ' ≠ 1 := by
  rintro rfl
  obtain ⟨μ, hμ, hact⟩ := hc.act_V1 ht h
  obtain ⟨μ', -, hact'⟩ := hc.act_V1 ht h'
  have key : ∀ c : K, μ * τ c = μ' * c := by
    intro c
    have h1 := (hact c).symm.trans (hact' c)
    have h2 := congrArg
      (fun X : Om4.VM K => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    simpa using h2
  have hμμ : μ = μ' := by simpa using key 1
  apply hτ
  ext c
  have h3 := key c
  rw [← hμμ] at h3
  rw [RingAut.one_apply]
  exact mul_left_cancel₀ hμ h3

variable {D : Subgroup G}

theorem mem_zpowers_of_sym (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    {ω : Kˣ} (hω : ω ≠ 1) {d₁ : G} (hd₁D : d₁ ∈ D) (hd₁L : d₁ ∈ fsuL0 T L)
    (hψd₁ : ψ ⟨d₁, hd₁L⟩ = (diagOf ω, diagOf ω)) {d : G} (hdD : d ∈ D) (hdL : d ∈ fsuL0 T L)
    {c : Kˣ} (hψd : ψ ⟨d, hdL⟩ = (diagOf c, diagOf c)) : d ∈ Subgroup.zpowers d₁ := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hK4]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hU hω (g' := c))
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hmem : d⁻¹ * d₁ ^ k ∈ D := D.mul_mem (D.inv_mem hdD) (D.zpow_mem hd₁D k)
  have hodd : Odd (orderOf (d⁻¹ * d₁ ^ k)) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hmem)
  have hψ1 : ψ (⟨d, hdL⟩⁻¹ * ⟨d₁, hd₁L⟩ ^ k) = 1 := by
    rw [map_mul, map_inv, map_zpow, hψd, hψd₁]
    have e1 : ((diagOf ω, diagOf ω) : SpecialLinearGroup (Fin 2) K ×
        SpecialLinearGroup (Fin 2) K) ^ k = (diagOf ω ^ k, diagOf ω ^ k) := rfl
    rw [e1, Prod.inv_mk, Prod.mk_mul_mk, ← diagHom_apply, ← diagHom_apply, ← map_zpow, ← map_inv,
      ← map_mul, hk, inv_mul_cancel, map_one, Prod.mk_one_one]
  have h1 := hc.eq_one_of_odd h37c h38c _ hodd hψ1
  have h3 : d⁻¹ * d₁ ^ k = 1 := h1
  rw [inv_mul_eq_one] at h3
  rw [h3]
  exact Subgroup.zpow_mem_zpowers d₁ k

theorem exists_vertex (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {A₀ B₀ : GL (Fin 2) K} {τ₀ : K ≃+* K} (hτ₀ : τ₀ ≠ 1)
    (hform₀ : bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A₀ B₀ * Om4.frM τ₀ * Om4.trM) :
    ∃ Dσ T₂ : Subgroup G, Dσ ≤ D ∧ Nat.card Dσ = 3 ∧
      (∀ x ∈ D, ∃ b ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
          ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G),
        ∃ d ∈ Dσ, x = b * d) ∧
      T₂ ≤ T ∧ t ∈ T₂ ∧ T ≤ Subgroup.normalizer (T₂ : Set G) ∧
      T ≤ Subgroup.normalizer ((Dσ ⊔ T₂ : Subgroup G) : Set G) ∧
      D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
          ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Dσ ⊔ T₂ : Subgroup G) : Set G) ∧
      IsSylowTwoOf T₂ (Dσ ⊔ T₂) ∧ T₂.relIndex (Dσ ⊔ T₂) = 3 ∧
      ¬ Dσ ⊔ T₂ ≤ Subgroup.normalizer (T₂ : Set G) ∧
      Nonempty (OTwoQuot (Dσ ⊔ T₂) ≃* Equiv.Perm (Fin 3)) ∧
      fsuV T I ≤ pCoreOf 2 (Dσ ⊔ T₂) ∧ Dσ ⊔ T₂ ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set B := D ⊓ Subgroup.centralizer (V₁ : Set G) with hB
  set R₀ := (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) with hR₀
  have : Nontrivial Kˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  obtain ⟨d₁, hd₁D, hd₁L, hψd₁⟩ := exists_mem_of_diag hdiag ω ω
  set Dσ := Subgroup.zpowers d₁ with hDσ
  have hDσD : Dσ ≤ D := (Subgroup.zpowers_le).mpr hd₁D
  have hd₁3 : d₁ ^ 3 = 1 := hc.pow_three_eq_one h37c h38c h2 hD hdiag hd₁D
  have hd₁1 : d₁ ≠ 1 := by
    intro h1
    have h3 : ψ ⟨d₁, hd₁L⟩ = 1 := by
      have : (⟨d₁, hd₁L⟩ : ↥(fsuL0 T L)) = 1 := Subtype.ext h1
      rw [this, map_one]
    rw [hψd₁] at h3
    have h4 := congrArg
      (fun p => ((p.1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h3
    simp [coe_diagOf] at h4
    exact hω h4
  have hd₁o : orderOf d₁ = 3 := orderOf_eq_prime hd₁3 hd₁1
  have hDσ3 : Nat.card Dσ = 3 := by rw [Nat.card_zpowers, hd₁o]
  have hinjD : ∀ x ∈ D, ∀ y ∈ D, ∀ (hx : x ∈ fsuL0 T L) (hy : y ∈ fsuL0 T L),
      ψ ⟨x, hx⟩ = ψ ⟨y, hy⟩ → x = y := by
    intro x hxD y hyD hx hy hxy
    have hmem : x⁻¹ * y ∈ D := D.mul_mem (D.inv_mem hxD) hyD
    have hodd : Odd (orderOf (x⁻¹ * y)) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hmem)
    have hψ1 : ψ (⟨x, hx⟩⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h1 := hc.eq_one_of_odd h37c h38c _ hodd hψ1
    have h3 : x⁻¹ * y = 1 := h1
    exact inv_mul_eq_one.mp h3
  have hsym : ∀ x ∈ D, ∃ b ∈ B, ∃ d ∈ Dσ, x = b * d := by
    intro x hx
    obtain ⟨b, hb, d, hdD, hdL, hdsym, rfl⟩ := hc.exists_mul_sym h2 hdiag hDL hx
    obtain ⟨a, a', haa⟩ := exists_diag_of_mem hdiag hdD hdL
    have haa' : a = a' := by
      rw [haa] at hdsym
      have h3 := congrArg
        (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hdsym
      simp only [coe_diagOf] at h3
      exact Units.ext (by simpa using h3)
    subst haa'
    exact ⟨b, hb, d, hc.mem_zpowers_of_sym h37c h38c h2 hD hω hd₁D hd₁L hψd₁ hdD hdL haa, rfl⟩
  have hR₀T : R₀ ≤ T := r0_le_T
  have hR₀2 : IsPGroup 2 R₀ := S.isPGroup_r0
  have hTR₀ : T ≤ Subgroup.normalizer (R₀ : Set G) := S.T_le_normalizer_r0
  have hDR₀ : D ≤ Subgroup.normalizer (R₀ : Set G) := hD.1.trans S.N0_le_normalizer_r0
  have hBR₀ : B ≤ Subgroup.normalizer (R₀ : Set G) := inf_le_left.trans hDR₀
  have hTLR : T ⊓ fsuL0 T L ≤ R₀ := le_sup_left
  set T₂ := cenMod T R₀ B with hT₂
  have hT₂T : T₂ ≤ T := cenMod_le T R₀ B
  have hR₀T₂ : R₀ ≤ T₂ := le_cenMod hR₀T
  have hTT₂ : T ≤ Subgroup.normalizer (T₂ : Set G) :=
    le_normalizer_cenMod_of_le hTR₀ hBR₀ (S.exists_mul_mem_r0_of_mem_B hD)
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hc.mul_comm_of_mem h37c h38c hD hdiag hx.1 hy.1
  have hBT₂ : B ≤ Subgroup.normalizer (T₂ : Set G) := le_normalizer_cenMod_of_comm hR₀T hBR₀ hBab
  obtain ⟨A, B', τ, hA, hB', hform⟩ := hc.exists_form_ut ht
  have hτ : τ ≠ 1 := hc.ne_one_of_forms ht (Or.inr hform₀) hform hτ₀
  rcases hform with hform | hform
  · exact absurd (hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c (Setup.T_le_fsuM ht) hform) htn
  have hfrob := frob_of_ne_one hK4 hτ
  have hmapτ : ∀ a : Kˣ, Units.map τ.toMonoidHom a = a ^ 2 := fun a => Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hfrob (a : K))
  have hconjL : ∀ s ∈ T, ∀ x ∈ fsuL0 T L, ∀ y ∈ fsuL0 T L, s * x * s⁻¹ * y⁻¹ ∈ fsuL0 T L :=
    fun s hs x hx y hy => (fsuL0 T L).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (Setup.T_le_normalizer_L0 hs) x).mp hx)
      ((fsuL0 T L).inv_mem hy)
  have htT₂ : t ∈ T₂ := by
    refine ⟨⟨ht, hTR₀ ht⟩, fun b hb => ?_⟩
    have hbD : b ∈ D := hb.1.1
    obtain ⟨a, a', haa⟩ := exists_diag_of_mem hdiag hbD (hDL hbD)
    have hprod : a * a' = 1 := (hc.mem_centralizer_V1_iff_diag ⟨b, hDL hbD⟩ a a' haa).mp hb.1.2
    obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ :=
      hc.conj_diag_swap h37c h38c hdiag ht hA hB' hform (hDL hbD) haa
    have ha3 := pow_three_eq_one_of_card_four hK4 a
    have hinv : a' = a⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have e1 : Units.map τ.toMonoidHom a' = a := by
      rw [hmapτ, hinv, inv_pow]
      calc (a ^ 2)⁻¹ = (a ^ 2)⁻¹ * a ^ 3 := by rw [ha3, mul_one]
        _ = a := by group
    have e2 : Units.map τ.toMonoidHom a = a' := by
      rw [hmapτ, hinv]
      calc a ^ 2 = a ^ 3 * a⁻¹ := by group
        _ = a⁻¹ := by rw [ha3, one_mul]
    rw [e1, e2, ← haa] at hψd'
    have hd'b : d' = b := hinjD d' hd'D b hbD hd'L (hDL hbD) hψd'
    rw [hd'b] at hmem hd'L
    exact hTLR ⟨hmem, hconjL t ht b (hDL hbD) b (hDL hbD)⟩
  have hconjd₁ : ∀ s ∈ T, s * d₁ * s⁻¹ ∈ R₀ ⊔ Dσ := by
    intro s hs
    obtain ⟨As, Bs, τs, hAs, hBs, hfs⟩ := hc.exists_form_ut hs
    have key : ∃ d' ∈ D, ∃ hd'L : d' ∈ fsuL0 T L, ψ ⟨d', hd'L⟩ =
        (diagOf (Units.map τs.toMonoidHom ω), diagOf (Units.map τs.toMonoidHom ω)) ∧
        s * d₁ * s⁻¹ * d'⁻¹ ∈ T := by
      rcases hfs with hfs | hfs
      · exact hc.conj_diag_ns h37c h38c hdiag hs hAs hBs hfs hd₁L hψd₁
      · exact hc.conj_diag_swap h37c h38c hdiag hs hAs hBs hfs hd₁L hψd₁
    obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ := key
    have hd'σ : d' ∈ Dσ :=
      hc.mem_zpowers_of_sym h37c h38c h2 hD hω hd₁D hd₁L hψd₁ hd'D hd'L hψd'
    have e : s * d₁ * s⁻¹ = (s * d₁ * s⁻¹ * d'⁻¹) * d' := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (hTLR ⟨hmem, hconjL s hs d₁ hd₁L d' hd'L⟩))
      (Subgroup.mem_sup_right hd'σ)
  have hTY : T ≤ Subgroup.normalizer ((R₀ ⊔ Dσ : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_sup_zpowers (hTR₀ hs) (hconjd₁ s hs)
  have hBY : B ≤ Subgroup.normalizer ((R₀ ⊔ Dσ : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_le_of_le hBR₀ ?_
    intro b hb
    refine mem_normalizer_of_conj_le fun y hy => ?_
    have hyD : y ∈ D := hDσD hy
    rw [show b * y * b⁻¹ = y by
      rw [hc.mul_comm_of_mem h37c h38c hD hdiag hb.1 hyD]
      group]
    exact hy
  have hDσR₀ : Dσ ≤ Subgroup.normalizer (R₀ : Set G) := hDσD.trans hDR₀
  have hinf : Dσ ⊓ R₀ = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hR₀2
    rw [hDσ3, hm]
    exact Nat.Coprime.pow_right m (by norm_num)
  have hidx : R₀.relIndex (R₀ ⊔ Dσ) = 3 := by
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' hDσR₀
    rw [sup_comm] at h1
    rw [h1, ← Subgroup.inf_relIndex_right, inf_comm, hinf, Subgroup.relIndex_bot_left, hDσ3]
  have hY2 : pCoreOf 2 (R₀ ⊔ Dσ) = R₀ := by
    have hZN : R₀ ⊔ Dσ ≤ Subgroup.normalizer (R₀ : Set G) :=
      sup_le Subgroup.le_normalizer hDσR₀
    have hsyl : IsSylowTwoOf R₀ (R₀ ⊔ Dσ) := ⟨le_sup_left, hR₀2, by
      show ¬ 2 ∣ R₀.relIndex (R₀ ⊔ Dσ)
      rw [hidx]
      norm_num⟩
    exact le_antisymm (F7.isSylowTwoOf_pCoreOf_le hsyl)
      (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer le_sup_left hZN hR₀2)
  obtain ⟨d', hd'D, hd'L, hψd', hmem⟩ :=
    hc.conj_diag_swap h37c h38c hdiag ht hA hB' hform hd₁L hψd₁
  have hd'eq : d' = d₁ ^ 2 := by
    refine hinjD d' hd'D (d₁ ^ 2) (D.pow_mem hd₁D 2) hd'L ((fsuL0 T L).pow_mem hd₁L 2) ?_
    rw [hψd']
    have e : (⟨d₁ ^ 2, (fsuL0 T L).pow_mem hd₁L 2⟩ : ↥(fsuL0 T L)) = ⟨d₁, hd₁L⟩ ^ 2 := rfl
    rw [e, map_pow, hψd₁, Prod.pow_mk, ← diagHom_apply, ← diagHom_apply, ← map_pow, hmapτ]
  have hnot : t * d₁ * t⁻¹ * d₁⁻¹ ∉ R₀ := by
    intro hR
    have hr : t * d₁ * t⁻¹ * (d₁ ^ 2)⁻¹ ∈ R₀ := by
      rw [← hd'eq]
      exact hTLR ⟨hmem, hconjL t ht d₁ hd₁L d' hd'L⟩
    have hd₁R : d₁ ∈ R₀ := by
      have e : d₁ = (t * d₁ * t⁻¹ * (d₁ ^ 2)⁻¹)⁻¹ * (t * d₁ * t⁻¹ * d₁⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem hr) hR
    have hodd : Odd (orderOf d₁) := by rw [hd₁o]; decide
    exact hd₁1 (eq_one_of_odd_of_mem hR₀2 hd₁R hodd)
  have hnt : ∃ r ∈ T₂, ∃ y ∈ R₀ ⊔ Dσ, r * y * r⁻¹ * y⁻¹ ∉ pCoreOf 2 (R₀ ⊔ Dσ) := by
    refine ⟨t, htT₂, d₁, Subgroup.mem_sup_right (Subgroup.mem_zpowers d₁), ?_⟩
    rw [hY2]
    exact hnot
  obtain ⟨hsyl, hidx₂, hS3⟩ := oTwoQuot_sup_iso_three (S.hyp.fsu.sylow.1.to_le hT₂T)
    (hT₂T.trans hTY) (by rw [hY2]; exact hidx) (by rw [hY2]; exact hR₀T₂) hnt
  have hL₂eq : (R₀ ⊔ Dσ) ⊔ T₂ = Dσ ⊔ T₂ :=
    le_antisymm (sup_le (sup_le (hR₀T₂.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  rw [hL₂eq] at hsyl hidx₂ hS3
  have hnn : ¬ Dσ ⊔ T₂ ≤ Subgroup.normalizer (T₂ : Set G) := by
    intro hN
    have hd₁Y : d₁ ∈ R₀ ⊔ Dσ := Subgroup.mem_sup_right (Subgroup.mem_zpowers d₁)
    have hd₁N := hN (Subgroup.mem_sup_left (Subgroup.mem_zpowers d₁))
    have h1 : d₁ * t⁻¹ * d₁⁻¹ ∈ T₂ :=
      (Subgroup.mem_normalizer_iff.mp hd₁N t⁻¹).mp (T₂.inv_mem htT₂)
    have hc1 : t * d₁ * t⁻¹ * d₁⁻¹ ∈ T₂ := by
      have e : t * d₁ * t⁻¹ * d₁⁻¹ = t * (d₁ * t⁻¹ * d₁⁻¹) := by group
      rw [e]
      exact T₂.mul_mem htT₂ h1
    have hc2 : t * d₁ * t⁻¹ * d₁⁻¹ ∈ R₀ ⊔ Dσ :=
      (R₀ ⊔ Dσ).mul_mem ((Subgroup.mem_normalizer_iff.mp (hTY ht) d₁).mp hd₁Y)
        ((R₀ ⊔ Dσ).inv_mem hd₁Y)
    have hsylY : IsSylowTwoOf R₀ (R₀ ⊔ Dσ) := ⟨le_sup_left, hR₀2, by
      show ¬ 2 ∣ R₀.relIndex (R₀ ⊔ Dσ)
      rw [hidx]
      norm_num⟩
    have hle : R₀ ⊔ (T₂ ⊓ (R₀ ⊔ Dσ)) ≤ R₀ :=
      KStar.le_of_isSylowTwoOf_of_le hsylY
        ((S.hyp.fsu.sylow.1.to_le hT₂T).to_le (sup_le hR₀T₂ inf_le_left)) le_sup_left
        (sup_le le_sup_left inf_le_right)
    exact hnot (hle (Subgroup.mem_sup_right ⟨hc1, hc2⟩))
  have hTL₂ : T ≤ Subgroup.normalizer ((Dσ ⊔ T₂ : Subgroup G) : Set G) := by
    rw [← hL₂eq]
    exact le_normalizer_sup_of_le_of_le hTY hTT₂
  have hBL₂ : B ≤ Subgroup.normalizer ((Dσ ⊔ T₂ : Subgroup G) : Set G) := by
    rw [← hL₂eq]
    exact le_normalizer_sup_of_le_of_le hBY hBT₂
  have hL₂M : Dσ ⊔ T₂ ≤ fsuM T L :=
    sup_le ((hDσD.trans hDL).trans Setup.L0_le_fsuM) (hT₂T.trans Setup.T_le_fsuM)
  have hVL₂ : fsuV T I ≤ pCoreOf 2 (Dσ ⊔ T₂) :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      (S.fsuV_le_Q.trans (le_sup_right.trans (hR₀T₂.trans le_sup_right)))
      (hL₂M.trans S.hMN) S.isPGroup_fsuV
  exact ⟨Dσ, T₂, hDσD, hDσ3, hsym, hT₂T, htT₂, hTT₂, hTL₂, hBL₂, hsyl, hidx₂, hnn, hS3, hVL₂,
    hL₂M⟩

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
