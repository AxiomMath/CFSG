module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep6D

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] abbrev wcSub (T L V V₁ : Subgroup G) : Subgroup G :=
  centerOf (i128 T L V V₁) ⊔ V₁

@[expose] abbrev kcSub (T L V V₁ : Subgroup G) (g : G) : Subgroup G :=
  centerOf (i128 T L V V₁) ⊔ CFSG.conjugate V₁ g

theorem mem_centerOf_iff' {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  unfold centerOf
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem conj_centerOf_mem {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {x : G} (hx : x ∈ centerOf X) : g * x * g⁻¹ ∈ centerOf X := by
  rw [mem_centerOf_iff'] at hx ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx.1, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ X := by
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) y).1 hy
    simpa using h
  have hc := hx.2 _ hy'
  calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * y := by group

theorem conj_centerOf_eq {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    CFSG.conjugate (centerOf X) g = centerOf X := by
  apply le_antisymm
  · intro x hx
    have h := (mem_conj'.1 hx)
    have h2 := conj_centerOf_mem (Subgroup.inv_mem _ hg) h
    simpa [mul_assoc] using h2
  · intro x hx
    exact mem_conj'.2 (conj_centerOf_mem hg hx)

theorem gN_i128 (h1289 : Lemma12_8_9W) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    g ∈ Subgroup.normalizer (i128 T L V V₁ : Set G) :=
  (h1289 G T L V 4 V₁ V₂ hs g hgP hgN).2.1 (p128_le_normalizer_V₂ hs hgP)

theorem conj_wc_eq_kc (h1289 : Lemma12_8_9W) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    CFSG.conjugate (wcSub T L V V₁) g = kcSub T L V V₁ g := by
  have hgI := gN_i128 h1289 hs hgP hgN
  have hsup : ∀ A B : Subgroup G, CFSG.conjugate (A ⊔ B) g =
      CFSG.conjugate A g ⊔ CFSG.conjugate B g := fun A B => by
    unfold CFSG.conjugate
    exact Subgroup.map_sup _ _ _
  unfold wcSub kcSub
  rw [hsup, conj_centerOf_eq hgI]

theorem centerOf_I2_le_zU (h12810 : Lemma12_8_10) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    centerOf (i128 T L V V₁) ≤ zU128 V V₁ := by
  have h := (h12810 G T L V 4 V₁ V₂ hs g hgP hgN).2.1
  intro x hx
  have hx' : x ∈ zU128 V V₁ ⊓ CFSG.conjugate (zU128 V V₁) g := by
    rw [h]; exact hx
  exact (Subgroup.mem_inf.1 hx').1

theorem V₁_le_zU (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂) :
    V₁ ≤ zU128 V V₁ := by
  intro z hz
  have hzV : z ∈ V ⊓ zU128 V V₁ := by
    rw [lemma12_8_8_three h1222 h12213 hs]; exact hz
  exact (Subgroup.mem_inf.1 hzV).2

theorem wcSub_le_zU (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12810 : Lemma12_8_10)
    {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂) {g : G}
    (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    wcSub T L V V₁ ≤ zU128 V V₁ :=
  sup_le (centerOf_I2_le_zU h12810 hs hgP hgN) (V₁_le_zU h1222 h12213 hs)

theorem Dg_mem_normalizers (h12813 : Lemma12_8_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) {d : G}
    (hd : d ∈ CFSG.conjugate (zU128 V V₁) g) :
    d ∈ Subgroup.normalizer (V₁ : Set G) ∧ d ∈ Subgroup.normalizer (u128 V V₁ : Set G) := by
  have hC := Dg_le_centralizer_V h12813 hs hgP hgN hd
  have hV₁V : V₁ ≤ V := hs.v1.1
  have hCC : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (V₁ : Set G) :=
    Subgroup.centralizer_le (fun x hx => hV₁V hx)
  have hN1 : d ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hCC hC)
  exact ⟨hN1, le_normalizer_conjClosure V _ hN1⟩

theorem kcSub_le_Dg (h1289 : Lemma12_8_9W) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    kcSub T L V V₁ g ≤ CFSG.conjugate (zU128 V V₁) g := by
  have hgI := gN_i128 h1289 hs hgP hgN
  apply sup_le
  · intro c hc
    rw [mem_conj']
    exact centerOf_I2_le_zU h12810 hs hgP hgN (conj_centerOf_mem hgI hc)
  · exact conj_mono' (V₁_le_zU h1222 h12213 hs) g

theorem ker_Dg (h12810 : Lemma12_8_10) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (D : HatModelU (u128 V V₁)) {d : G}
    (hd : d ∈ CFSG.conjugate (zU128 V V₁) g) (hdN1 : d ∈ Subgroup.normalizer (V₁ : Set G))
    (hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G)) :
    D.ρ ⟨d, hdN⟩ = 1 ↔ d ∈ kcSub T L V V₁ g := by
  have hA6 := (h12810 G T L V 4 V₁ V₂ hs g hgP hgN).2.2.2.2.2
  have key : CFSG.conjugate (zU128 V V₁) g ⊓
      centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
        kcSub T L V V₁ g := by
    rw [hA6.1, hA6.2.1, hA6.2.2.1, hA6.2.2.2.1, hA6.2.2.2.2.1]
  have hmem : d ∈ centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G))
      (u128 V V₁) ↔ D.ρ ⟨d, hdN⟩ = 1 := by
    rw [L128A.HatU.rho_eq_one_iff]
    constructor
    · intro h
      exact fun u hu => h.2.2 u hu
    · intro h
      refine ⟨hdN1, CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) hdN, ?_⟩
      exact fun u hu => h u hu
  rw [← hmem, ← key]
  exact ⟨fun h => Subgroup.mem_inf.2 ⟨hd, h⟩, fun h => (Subgroup.mem_inf.1 h).2⟩

end Defs

section Card

variable {G : Type} [Group G] [Finite G]

theorem card_zU_eq (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (D : HatModelU (u128 V V₁))
    (hDg4 : Nat.card ↥(D.img (CFSG.conjugate (zU128 V V₁) g)) = 4) :
    Nat.card ↥(zU128 V V₁) = 4 * Nat.card ↥(wcSub T L V V₁) := by
  classical
  set Dg := CFSG.conjugate (zU128 V V₁) g with hDg
  have hDgU : Dg ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun d hd =>
    (Dg_mem_normalizers h12813 hs hgP hgN hd).2
  have hDgN1 : ∀ d ∈ Dg, d ∈ Subgroup.normalizer (V₁ : Set G) := fun d hd =>
    (Dg_mem_normalizers h12813 hs hgP hgN hd).1
  set ρDg : ↥Dg →* (D.V ≃ₗ[ZMod 2] D.V) := D.ρ.comp (Subgroup.inclusion hDgU) with hρDg
  have hrange : ρDg.range = D.img Dg := (L1294.img_eq_range D hDgU).symm
  have hkerK : ρDg.ker.map Dg.subtype = kcSub T L V V₁ g := by
    ext d
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxD : (x : G) ∈ Dg := x.2
      have hx' : D.ρ ⟨(x : G), hDgU hxD⟩ = 1 := by
        have := (MonoidHom.mem_ker.1 hx)
        exact this
      exact (ker_Dg h12810 hs hgP hgN D hxD (hDgN1 _ hxD) (hDgU hxD)).1 hx'
    · intro hd
      have hdD : d ∈ Dg := kcSub_le_Dg h1289 h1222 h12213 h12810 hs hgP hgN hd
      refine ⟨⟨d, hdD⟩, ?_, rfl⟩
      show D.ρ ⟨d, hDgU hdD⟩ = 1
      exact (ker_Dg h12810 hs hgP hgN D hdD (hDgN1 _ hdD) (hDgU hdD)).2 hd
  have hcardKer : Nat.card ↥ρDg.ker = Nat.card ↥(kcSub T L V V₁ g) := by
    rw [← hkerK, Subgroup.card_map_of_injective Dg.subtype_injective]
  have hsplit := Subgroup.card_ker_mul_card_range ρDg
  rw [hrange, hDg4, hcardKer] at hsplit
  have hconjZ : Nat.card ↥Dg = Nat.card ↥(zU128 V V₁) := by
    rw [hDg]
    unfold CFSG.conjugate
    rw [Subgroup.card_map_of_injective]
    intro a b hab
    exact (MulAut.conj g⁻¹).injective hab
  have hconjW : Nat.card ↥(kcSub T L V V₁ g) = Nat.card ↥(wcSub T L V V₁) := by
    rw [← conj_wc_eq_kc h1289 hs hgP hgN]
    unfold CFSG.conjugate
    rw [Subgroup.card_map_of_injective]
    intro a b hab
    exact (MulAut.conj g⁻¹).injective hab
  rw [← hconjZ, ← hsplit, hconjW, mul_comm]

end Card

section Fstar

variable {G : Type} [Group G] [Finite G]

theorem F_star (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F3 : FactF3)
    {T L V V₁ V₂ K₁ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    (hLK : lOne L V₁ ≤ K₁) (hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G))
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁))
    (hTΩ : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ D.img K₁)
    (hker : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    (S : Submodule (ZMod 2) D.V)
    (hSV : ∀ v ∈ V, D.π v ∈ S) (hSπ : ∀ s ∈ S, ∃ v ∈ V, D.π v = s)
    {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hM : Module.finrank (ZMod 2) M = 4)
    (kap : ↥(D.img K₁) ≃* (M ≃ₗ[ZMod 2] M))
    (p ℓ Pl : Submodule (ZMod 2) M) (hp : Module.finrank (ZMod 2) p = 1)
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hPl : Module.finrank (ZMod 2) Pl = 3)
    (hpℓ : p < ℓ) (hℓPl : ℓ < Pl)
    (hY₁ : kmapOf (D.img K₁) kap (stabS (Submodule.span (ZMod 2) {D.π a})) = stabS ℓ)
    (hY₂ : kmapOf (D.img K₁) kap (stabS S) = stabS p ∨
      kmapOf (D.img K₁) kap (stabS S) = stabS Pl)
    (hD0 : kmapOf (D.img K₁) kap (D.img (CFSG.conjugate (zU128 V V₁) g)) =
      pCoreOf 2 (kmapOf (D.img K₁) kap (stabS S)) ⊓ pCoreOf 2 (stabS ℓ))
    {y₀ : G} (hy₀ : y₀ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G)) (hy₀3 : orderOf y₀ = 3)
    {x : G} (hx : x ∈ zU128 V V₁) (hxW : y₀ * x * y₀⁻¹ * x⁻¹ ∈ wcSub T L V V₁) :
    x ∈ wcSub T L V V₁ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hcx.hyp.hyp.irrPlus.2.2.1
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hcx.hyp.hyp.normalizes
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    (sup_le Subgroup.le_normalizer hTN) hgP.1
  have hgV₂ : g ∈ Subgroup.normalizer (V₂ : Set G) := p128_le_normalizer_V₂ hs hgP
  have hy₀L : y₀ ∈ L := (Subgroup.mem_inf.1 hy₀).1
  have hy₀C : y₀ ∈ Subgroup.centralizer (V₂ : Set G) := (Subgroup.mem_inf.1 hy₀).2
  set y₁ : G := g⁻¹ * y₀ * g with hy₁def
  have hy₁L : y₁ ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgL) y₀).1 hy₀L
    simpa [hy₁def] using h
  have hy₁C : y₁ ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : g * v * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 hgV₂ v).1 hv
    have hc := Subgroup.mem_centralizer_iff.1 hy₀C _ hw
    calc v * y₁ = g⁻¹ * ((g * v * g⁻¹) * y₀) * g := by rw [hy₁def]; group
      _ = g⁻¹ * (y₀ * (g * v * g⁻¹)) * g := by rw [hc]
      _ = y₁ * v := by rw [hy₁def]; group
  have hy₁3 : orderOf y₁ = 3 := by
    have h := conj_orderOf g⁻¹ y₀
    rw [inv_inv] at h
    rw [hy₁def, h, hy₀3]
  have hy₁K : y₁ ∈ K₁ :=
    L0_le_K₁ hLK hs.le (Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hy₁L, hy₁C⟩,
      by rw [hy₁3]; decide⟩)
  have hy₁U : y₁ ∈ Subgroup.normalizer (u128 V V₁ : Set G) := hK₁U hy₁K
  have hy₁H : y₁ ∈ Subgroup.normalizer (V₁ : Set G) := hK₁H hy₁K
  have hy₁V : y₁ ∈ Subgroup.normalizer (V : Set G) := hLV hy₁L
  have hρ₁ : D.ρ ⟨y₁, hy₁U⟩ ∈ D.img K₁ := L128A.HatU.rho_mem_img D hy₁K hy₁U
  have hρ₁S : D.ρ ⟨y₁, hy₁U⟩ ∈ stabS S := rho_stab_S D hSV hSπ hy₁V hy₁U
  have hca : y₁ * a * y₁⁻¹ = a := by
    rw [← Subgroup.mem_centralizer_iff.1 hy₁C a haV₂]
    group
  have hρ₁fix : D.ρ ⟨y₁, hy₁U⟩ (D.π a) = D.π a := by
    rw [D.ρ_π ⟨y₁, hy₁U⟩ a (le_conjClosure V _ (hs.v2.1 haV₂)), hca]
  have hρ₁span : D.ρ ⟨y₁, hy₁U⟩ ∈ stabS (Submodule.span (ZMod 2) {D.π a}) :=
    mem_stabS_span_of_fix hρ₁fix
  set k₁ : ↥(D.img K₁) := ⟨D.ρ ⟨y₁, hy₁U⟩, hρ₁⟩ with hk₁
  have hγS : kap k₁ ∈ kmapOf (D.img K₁) kap (stabS S) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hρ₁S)
  have hγℓ : kap k₁ ∈ stabS ℓ := by
    have h : kap k₁ ∈ kmapOf (D.img K₁) kap (stabS (Submodule.span (ZMod 2) {D.π a})) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hρ₁span)
    rw [hY₁] at h
    exact h
  have hy₁3' : y₁ ^ 3 = 1 := by rw [← hy₁3]; exact pow_orderOf_eq_one y₁
  have hh1 : (⟨y₁, hy₁U⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hy₁3')
  have hk₁3 : k₁ ^ 3 = 1 := by
    apply Subtype.ext
    show (D.ρ ⟨y₁, hy₁U⟩) ^ 3 = 1
    rw [← map_pow, hh1, map_one]
  have hγ3 : kap k₁ ^ 3 = 1 := by rw [← map_pow, hk₁3, map_one]
  have hγ1 : kap k₁ ≠ 1 := by
    intro h
    have hk : k₁ = 1 := kap.injective (h.trans (map_one kap).symm)
    have hρ : D.ρ ⟨y₁, hy₁U⟩ = 1 := congrArg Subtype.val hk
    exact order_three_not_mem_two_group (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
      ((hker y₁ hy₁K hy₁U).1 hρ) hy₁3
  have hγord : orderOf (kap k₁) = 3 := orderOf_eq_prime hγ3 hγ1
  set d : G := g⁻¹ * x * g with hd_def
  have hgd : g * d * g⁻¹ = x := by rw [hd_def]; group
  have hdZ : d ∈ CFSG.conjugate (zU128 V V₁) g := mem_conj'.2 (by rw [hgd]; exact hx)
  have hdN1 : d ∈ Subgroup.normalizer (V₁ : Set G) := (Dg_mem_normalizers h12813 hs hgP hgN hdZ).1
  have hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G) :=
    (Dg_mem_normalizers h12813 hs hgP hgN hdZ).2
  have hdT : d ∈ T := Dg_le_T h1222 h1289 hcx hs hgP hgN hdZ
  have hρdΩ : D.ρ ⟨d, hdN⟩ ∈ D.img K₁ := hTΩ d hdT hdN
  have hρdDg : D.ρ ⟨d, hdN⟩ ∈ D.img (CFSG.conjugate (zU128 V V₁) g) :=
    L128A.HatU.rho_mem_img D hdZ hdN
  set κd : ↥(D.img K₁) := ⟨D.ρ ⟨d, hdN⟩, hρdΩ⟩ with hκd_def
  have hκd_mem : kap κd ∈ pCoreOf 2 (kmapOf (D.img K₁) kap (stabS S)) ⊓ pCoreOf 2 (stabS ℓ) := by
    rw [← hD0]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hρdDg)
  set c : G := y₁ * d * y₁⁻¹ * d⁻¹ with hc_def
  have hcK : c ∈ kcSub T L V V₁ g := by
    rw [← conj_wc_eq_kc h1289 hs hgP hgN, mem_conj']
    have e : g * c * g⁻¹ = y₀ * x * y₀⁻¹ * x⁻¹ := by
      rw [hc_def, hy₁def, hd_def]; group
    rw [e]
    exact hxW
  have hcZ : c ∈ CFSG.conjugate (zU128 V V₁) g :=
    kcSub_le_Dg h1289 h1222 h12213 h12810 hs hgP hgN hcK
  have hcN1 : c ∈ Subgroup.normalizer (V₁ : Set G) := (Dg_mem_normalizers h12813 hs hgP hgN hcZ).1
  have hcU : c ∈ Subgroup.normalizer (u128 V V₁ : Set G) :=
    (Dg_mem_normalizers h12813 hs hgP hgN hcZ).2
  have hρc : D.ρ ⟨c, hcU⟩ = 1 := (ker_Dg h12810 hs hgP hgN D hcZ hcN1 hcU).2 hcK
  have hcomm : D.ρ ⟨y₁, hy₁U⟩ * D.ρ ⟨d, hdN⟩ = D.ρ ⟨d, hdN⟩ * D.ρ ⟨y₁, hy₁U⟩ := by
    have e : (⟨c, hcU⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) =
        ⟨y₁, hy₁U⟩ * ⟨d, hdN⟩ * ⟨y₁, hy₁U⟩⁻¹ * ⟨d, hdN⟩⁻¹ :=
      Subtype.ext (by simp [hc_def, mul_assoc])
    have h := hρc
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h
    calc D.ρ ⟨y₁, hy₁U⟩ * D.ρ ⟨d, hdN⟩
        = (D.ρ ⟨y₁, hy₁U⟩ * D.ρ ⟨d, hdN⟩ * (D.ρ ⟨y₁, hy₁U⟩)⁻¹ * (D.ρ ⟨d, hdN⟩)⁻¹) *
            (D.ρ ⟨d, hdN⟩ * D.ρ ⟨y₁, hy₁U⟩) := by group
      _ = D.ρ ⟨d, hdN⟩ * D.ρ ⟨y₁, hy₁U⟩ := by rw [h, one_mul]
  have hconjκ : kap k₁ * kap κd * (kap k₁)⁻¹ = kap κd := by
    have e2 : k₁ * κd * k₁⁻¹ = κd := by
      apply Subtype.ext
      show D.ρ ⟨y₁, hy₁U⟩ * D.ρ ⟨d, hdN⟩ * (D.ρ ⟨y₁, hy₁U⟩)⁻¹ = D.ρ ⟨d, hdN⟩
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [← map_inv, ← map_mul, ← map_mul, e2]
  have hfp := fpf_D0 F3 hM p ℓ Pl hp hℓ hPl hpℓ hℓPl _ hY₂ hγord hγℓ hγS
    (kap κd) hκd_mem hconjκ
  have hκ1 : kap κd = 1 := hfp
  have hk1 : κd = 1 := kap.injective (hκ1.trans (map_one kap).symm)
  have hρd1 : D.ρ ⟨d, hdN⟩ = 1 := congrArg Subtype.val hk1
  have hdKc : d ∈ kcSub T L V V₁ g := (ker_Dg h12810 hs hgP hgN D hdZ hdN1 hdN).1 hρd1
  have hdW : d ∈ CFSG.conjugate (wcSub T L V V₁) g := by
    rw [conj_wc_eq_kc h1289 hs hgP hgN]
    exact hdKc
  have := mem_conj'.1 hdW
  rw [hgd] at this
  exact this

end Fstar

end CFSG.Quasithin.H13.C1294
