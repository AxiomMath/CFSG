module

public import CFSG.Quasithin.H13.A6S13816p
public import CFSG.Quasithin.H13.A6S13816q
public import CFSG.Quasithin.EmptyFaithful.S1565G
public import CFSG.Quasithin.EmptyFaithful.S153MTwoK
public import CFSG.Quasithin.Background.F918C12
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.F918C8

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

namespace L2Ten

variable {G : Type} [Group G]

theorem nonempty_quot_mulEquiv {K X : Type} [Group K] [Group X] {N : Subgroup K} [N.Normal]
    [IsSimpleGroup (K ⧸ N)] [Nontrivial X] (f : K →* X) (hf : Function.Surjective f)
    (hN : N ≤ f.ker) : Nonempty (K ⧸ N ≃* X) := by
  set g := QuotientGroup.lift N f hN with hg
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨k, rfl⟩ := hf x
    exact ⟨k, rfl⟩
  have hgi : Function.Injective g := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff g).mp h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : X)
      obtain ⟨q, rfl⟩ := hgs x
      have hq : q ∈ g.ker := h ▸ Subgroup.mem_top q
      exact hx (MonoidHom.mem_ker.mp hq)
  exact ⟨MulEquiv.ofBijective g ⟨hgi, hgs⟩⟩

theorem comm_mem_of_commV_le {W U H : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W U))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ≤ Subgroup.normalizer (W : Set G)) {X Y : Subgroup ↥H}
    (h : commV (X.map (actH hWN hUN)) ≤ fixV (Y.map (actH hWN hUN))) {g : G} (hg : g ∈ U)
    {x y : ↥H} (hx : x ∈ X) (hy : y ∈ Y) :
    (y : G) * ((x : G) * g * (x : G)⁻¹ * g⁻¹) * (y : G)⁻¹ *
      ((x : G) * g * (x : G)⁻¹ * g⁻¹)⁻¹ ∈ W := by
  have hxg : (x : G) * g * (x : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUN x.2) g).mp hg
  have hc : (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈ U := U.mul_mem hxg (U.inv_mem hg)
  have h1 : modMk hUW _ hc ∈ commV (X.map (actH hWN hUN)) := by
    apply Subgroup.subset_closure
    refine ⟨actH hWN hUN x, ⟨x, hx, rfl⟩, modMk hUW g hg, ?_⟩
    rw [actH_modMk hWN hUW hUN x hg, ← modMk_inv hUW hg, ← modMk_mul hUW hxg (U.inv_mem hg)]
  have h2 := h h1 (actH hWN hUN y) ⟨y, hy, rfl⟩
  rw [actH_modMk hWN hUW hUN y hc] at h2
  exact (S153M.modMk_conj_eq_iff hUW hc _).mp h2

theorem false_of_sum {V₁ U H : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf V₁ U))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hUV : U ≤ Subgroup.normalizer (V₁ : Set G)) (Wm : Subgroup ↥(tildeOf V₁ U))
    {XA XB : Subgroup ↥H}
    (hCA : ∀ w, (∀ x ∈ XA, actH hV₁ hUN x w * w⁻¹ ∈ Wm) → w ∈ Wm)
    (hCB : ∀ w, (∀ y ∈ XB, actH hV₁ hUN y w * w⁻¹ ∈ Wm) → w ∈ Wm) {W₀ W₁ : Subgroup G}
    (hW₀ : ∀ g (hg : g ∈ U), g ∈ W₀ → modMk hUV g hg ∈ Wm)
    (hW₁ : ∃ g, ∃ hg : g ∈ U, g ∈ W₁ ∧ modMk hUV g hg ∉ Wm)
    (hsum : ∀ g ∈ W₁, ∀ x ∈ XA, ∀ y ∈ XB, (y : G) * ((x : G) * g * (x : G)⁻¹ * g⁻¹) *
      (y : G)⁻¹ * ((x : G) * g * (x : G)⁻¹ * g⁻¹)⁻¹ ∈ W₀) : False := by
  obtain ⟨g, hgU, hgW, hgm⟩ := hW₁
  refine hgm (hCA _ fun x hx => ?_)
  have hxg : (x : G) * g * (x : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hUN x.2) g).mp hgU
  have hc : (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈ U := U.mul_mem hxg (U.inv_mem hgU)
  have e : actH hV₁ hUN x (modMk hUV g hgU) * (modMk hUV g hgU)⁻¹ = modMk hUV _ hc := by
    rw [actH_modMk hV₁ hUV hUN x hgU, ← modMk_inv hUV hgU, ← modMk_mul hUV hxg (U.inv_mem hgU)]
  rw [e]
  refine hCB _ fun y hy => ?_
  have hyc : (y : G) * ((x : G) * g * (x : G)⁻¹ * g⁻¹) * (y : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hUN y.2) _).mp hc
  rw [actH_modMk hV₁ hUV hUN y hc, ← modMk_inv hUV hc, ← modMk_mul hUV hyc (U.inv_mem hc)]
  exact hW₀ _ _ (hsum g hgW x hx y hy)

theorem fix_conj {V₁ U H : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf V₁ U))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (Wm : Subgroup ↥(tildeOf V₁ U)) (hWm : ∀ x : ↥H, ∀ w ∈ Wm, actH hV₁ hUN x w ∈ Wm)
    {X : Subgroup ↥H} (hC : ∀ w, (∀ x ∈ X, actH hV₁ hUN x w * w⁻¹ ∈ Wm) → w ∈ Wm) (s : ↥H) :
    ∀ w, (∀ y ∈ X.map (MulAut.conj s).toMonoidHom, actH hV₁ hUN y w * w⁻¹ ∈ Wm) → w ∈ Wm := by
  intro w hw
  have h1 : actH hV₁ hUN s⁻¹ w ∈ Wm := by
    refine hC _ fun x hx => ?_
    have h2 := hWm s⁻¹ _ (hw (s * x * s⁻¹) ⟨x, hx, rfl⟩)
    have e : actH hV₁ hUN s⁻¹ (actH hV₁ hUN (s * x * s⁻¹) w * w⁻¹) =
        actH hV₁ hUN x (actH hV₁ hUN s⁻¹ w) * (actH hV₁ hUN s⁻¹ w)⁻¹ := by
      rw [map_mul (actH hV₁ hUN s⁻¹), map_inv (actH hV₁ hUN s⁻¹)]
      congr 1
      rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
      congr 2
      group
    rwa [e] at h2
  have h3 := hWm s _ h1
  rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h3

theorem twoSum_sec [Finite G] (hA21 : AsA21SQTKSection) (h56 : AsB56)
    {T V L V₁ Vp H K : Subgroup G} (hF : HypF918 T V L V₁ Vp H K) (hS : SQTKGroup ↥H)
    (hHK : H = K ⊔ T) {t : G} (htT : t ∈ T) (hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp H)
    (hK₀eq : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 H)
    (hperm : ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K : Set G))
    {n : ℕ} (hn : IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K))
    {W U : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W U))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ≤ Subgroup.normalizer (W : Set G))
    (hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWN hUN x = 1)
    (hnt : ¬ (conjClosure K T).subgroupOf H ≤ (actH hWN hUN).ker)
    (hFF : IsFFModule (actH hWN hUN).range) :
    (∀ g ∈ U, ∀ a ∈ K, ∀ b ∈ K.map (MulAut.conj t).toMonoidHom,
      b * (a * g * a⁻¹ * g⁻¹) * b⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ W) ∧
      ¬ IsStrongFFModule (actH hWN hUN).range := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  have htH : t ∈ H := hF.T_le_H htT
  have hFE : Fact (IsElemAbelian 2 (tildeOf W U)) := inferInstance
  have hV : ∀ v : ↥(tildeOf W U), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hFE.out.2 v v.2)
  set t' : ↥H := ⟨t, htH⟩ with ht'
  set φ := actH hWN hUN with hφ
  have hmapconj := S153M.map_conj_subgroupOf hKH htH
  have hsup : K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom =
      (conjClosure K T).subgroupOf H := by
    rw [hmapconj, ← Subgroup.subgroupOf_sup hKH hKtH, hK₀eq]
  have hqK := S153M.isQuasisimple_subgroupOf hKH hF.K_quasisimple
  have hKn : (K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom).Normal := by
    rw [hsup]
    exact S153M.normal_subgroupOf_of_le (K := conjClosure K T) hF.K₀_le_H hF.K₀_normal
  have hcomm' : ⁅K.subgroupOf H, (K.subgroupOf H).map (MulAut.conj t').toMonoidHom⁆ ≤
      CFSG.pCore 2 ↥H := by
    rw [hmapconj]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine S153M.mem_pCore_of_mem_pCoreOf _ (hcomm ?_)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
  have hQ' : CFSG.pCore 2 ↥H ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine hQ x ?_
    have hx' : x ∈ CFSG.Open.pCore 2 ↥H := hx
    exact Subgroup.mem_map.mpr ⟨x, hx', rfl⟩
  have hTK₀ : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
  have hHK₀ : H = conjClosure K T ⊔ T :=
    le_antisymm (hHK ▸ sup_le_sup_right (le_conjClosure K T) T) hF.K₀T_le_H
  have h2' : ∀ y : ↥H, ∃ e : ℕ, y ^ 2 ^ e ∈
      K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom := by
    intro y
    rw [hsup]
    exact S153M.exists_two_pow_mem hHK₀ hF.sylow_H.2.1 hTK₀ y
  have hperm' : ∀ x : ↥H, x ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∨
      t'⁻¹ * x ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro x
    have key : ∀ y : ↥H, (y : G) ∈ Subgroup.normalizer (K : Set G) →
        y ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact Subgroup.mem_normalizer_iff.mp hy (h : G)
    rcases hperm x x.2 with h | h
    · exact Or.inl (key x h)
    · exact Or.inr (key (t'⁻¹ * x) (by simpa [ht'] using h))
  have hnt' : ¬ K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom ≤ φ.ker := by
    rw [hsup]
    exact hnt
  have hKnt : ¬ K.subgroupOf H ≤ φ.ker := by
    intro h
    apply hnt'
    refine sup_le h ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk1 : φ k = 1 := MonoidHom.mem_ker.mp (h hk)
    rw [MonoidHom.mem_ker]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hk1, mul_one,
      mul_inv_cancel]
  let ρ₁ : ↥K →* ↥((K.subgroupOf H).map φ) :=
    (φ.comp (Subgroup.inclusion hKH)).codRestrict ((K.subgroupOf H).map φ) fun k =>
      ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hρ₁ : Function.Surjective ρ₁ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hne₁ : Nontrivial ↥((K.subgroupOf H).map φ) := by
    by_contra hcon
    have hsub : Subsingleton ↥((K.subgroupOf H).map φ) := not_nontrivial_iff_subsingleton.mp hcon
    apply hKnt
    intro k hk
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨φ k, k, hk, rfl⟩ : ↥((K.subgroupOf H).map φ)) 1)
  have hker : CFSG.pCore 2 ↥K ≤ ρ₁.ker := by
    intro k hk
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk' : (k : G) ∈ pCoreOf 2 H :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp)
        ((mem_pCore_iff k).1 hk)
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (hQ _ hk')
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hn).2
  obtain ⟨e⟩ := nonempty_quot_mulEquiv ρ₁ hρ₁ hker
  have hK : IsPSL 2 2 n ↥((K.subgroupOf H).map φ) := isPSL_congr e hn
  obtain ⟨hsum, hns⟩ := FFTwo.twoSum_of_action hA21 h56 hS hV φ (K.subgroupOf H) t' hqK hKn
    hcomm' hQ' h2' hperm' hnt' hFF hK
  refine ⟨fun g hg a ha b hb => ?_, hns⟩
  obtain ⟨κ, hκ, rfl⟩ := hb
  have h1 := comm_mem_of_commV_le hWN hUN hUW hsum hg (x := ⟨a, hKH ha⟩)
    (y := t' * ⟨κ, hKH hκ⟩ * t'⁻¹) (Subgroup.mem_subgroupOf.mpr ha)
    ⟨⟨κ, hKH hκ⟩, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
  simpa [ht', MulAut.conj_apply] using h1

theorem omega4PlusModule_of_autSub_top {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {U : Subgroup W} (hU : U = ⊤) {m : ℕ} (h : Omega4PlusModule (autSub X U) m) :
    Omega4PlusModule X m := by
  subst hU
  obtain ⟨F, hF, hFin, hcard, hr⟩ := h
  refine ⟨F, hF, hFin, hcard, FFModel.Realizes.of_autSub (fun g _ => mem_stabSub_top g)
    (fun g _ u => ?_) bot_le ?_ ?_⟩
  · rw [Subgroup.mem_bot, Subgroup.mem_bot]
    exact map_eq_one_iff g g.injective
  · exact eq_bot_iff.mpr fun g hg =>
      Subgroup.mem_bot.mpr (MulEquiv.ext fun u => hg.2 u (Subgroup.mem_top u))
  · rwa [Subgroup.bot_subgroupOf]

theorem omega4PlusModule_congr {V₁ X A B : Subgroup G} (h : A = B)
    [Fact (IsElemAbelian 2 (tildeOf V₁ A))] [Fact (IsElemAbelian 2 (tildeOf V₁ B))] {m : ℕ}
    (hA : Omega4PlusModule (autOn (tildeOf V₁ X) (tildeOf V₁ A)) m) :
    Omega4PlusModule (autOn (tildeOf V₁ X) (tildeOf V₁ B)) m := by
  subst h
  exact hA

theorem isFFModule_of_isStrongFFModule {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (h : IsStrongFFModule X) : IsFFModule X := by
  obtain ⟨A, hA, hne, hel, hlt⟩ := h
  exact ⟨A, hA, hne, hel, hlt.le⟩

theorem card_psl_lt {n m : ℕ} (h : n < m) : 2 ^ n * (4 ^ n - 1) < 2 ^ m * (4 ^ m - 1) := by
  have ha : 2 ^ n < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) h
  have hc : 4 ^ n < 4 ^ m := Nat.pow_lt_pow_right (by norm_num) h
  have hd : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  exact Nat.mul_lt_mul'' ha (by omega)

theorem eq_of_isPSL_two_two {X : Type} [Group X] {n m : ℕ} (hn : IsPSL 2 2 n X)
    (hm : IsPSL 2 2 m X) : n = m := by
  have h1 := CFSG.Quasithin.card_of_isPSL_two_even hn.1.2.1 hn
  have h2 := CFSG.Quasithin.card_of_isPSL_two_even hm.1.2.1 hm
  rcases lt_trichotomy n m with h | h | h
  · exact absurd (h1.symm.trans h2) (card_psl_lt h).ne
  · exact h
  · exact absurd (h2.symm.trans h1) (card_psl_lt h).ne

end L2Ten

@[expose] def Case13816L2HatOrth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      IsPSL 2 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) →
      ∀ [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))],
        Omega4PlusModule (S.KSt H (conjClosure K T)) 2 → False

theorem case13816L2HatTensor_of
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h1337 : Stmt13_3_7) (h13 : Lem13813) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (hA21 : AsA21SQTKSection) (h56 : AsB56) (hOrth : Case13816L2HatOrth) :
    Case13816L2HatTensor := by
  intro G _ _ T L V S hS hhat H hH K hK hne hHeq hL2 Wm hWmne hWmi _ hC
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36 h37 h38 h139 h1334 h13 hS hH hK
  rw [← hHeq] at hF
  have hHq : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  obtain ⟨n, hn⟩ : ∃ n, IsPSL 2 2 n (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hL2 with h | h
    · exact h
    · exact ⟨2, C126.isPSL_two_two_two_of_alternating_five _ h⟩
  have hn2 : n = 2 := S.n_eq_two_of_hat h37 h38 h122 h1334 h1337 h13 hS hhat hH hK hne hn
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hn).2
  have hℓK : S.L1 ≤ conjClosure K T :=
    S.L1_le_conjClosure' h37 h38 h122 hH hK hne (L2Case.three_dvd_card hL2)
  have hK₀KT : conjClosure K T ≤ K ⊔ T := conjClosure_le fun s hs k hk =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left hk))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hs))
  have hHK : H = K ⊔ T := by
    rw [hHeq]
    exact sup_eq_left.mpr (hℓK.trans hK₀KT)
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  obtain ⟨hKt, hK₀eq, hcomm, hperm⟩ := (five_group_data hF hHq h37 h38 hne).2 t htT htK
  have htH : t ∈ H := hF.T_le_H htT
  set t' : ↥H := ⟨t, htH⟩ with ht'
  have hV₁ : H ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) := hF.H_le_normalizer_V₁
  have hUN : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  have hUV : conjClosure S.V3 H ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure S.V3 H)
  have hFU := factElem hF (le_conjClosure S.V3 H)
  have hCK : ∀ w, (∀ x ∈ K.subgroupOf H, actH hV₁ hUN x w * w⁻¹ ∈ Wm) → w ∈ Wm := by
    intro w hw
    refine hC w fun k hk => ?_
    rw [Setting4.KSt, autOn_tilde_eq_map_actH hV₁ hUN hKH] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    exact hw x hx
  have hWmH : ∀ x : ↥H, ∀ w ∈ Wm, actH hV₁ hUN x w ∈ Wm := fun x w hw => by
    refine hWmi _ ?_ w hw
    rw [Setting4.KSt, autOn_tilde_eq_map_actH hV₁ hUN le_rfl]
    exact ⟨x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hCKt := L2Ten.fix_conj hV₁ hUN Wm hWmH hCK t'
  have hKtsub : (K.subgroupOf H).map (MulAut.conj t').toMonoidHom =
      (K.map (MulAut.conj t).toMonoidHom).subgroupOf H := S153M.map_conj_subgroupOf hKH htH
  have hout : ∃ g, ∃ hg : g ∈ conjClosure S.V3 H, modMk hUV g hg ∉ Wm := by
    by_contra hcon
    push Not at hcon
    apply hWmne
    rw [eq_top_iff]
    intro w _
    obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde w
    have hw : w = modMk hUV (a : G) haU := Subtype.ext haw.symm
    rw [hw]
    exact hcon _ haU
  have hW₀V : ∀ g (hg : g ∈ conjClosure S.V3 H), g ∈ fsuV1 T V → modMk hUV g hg ∈ Wm := by
    intro g hg hgV
    rw [(S153M.modMk_eq_one_iff hUV hg).mpr hgV]
    exact Wm.one_mem
  have hfin : ∀ {W₀ W₁ : Subgroup G},
      (∀ g (hg : g ∈ conjClosure S.V3 H), g ∈ W₀ → modMk hUV g hg ∈ Wm) →
      (∃ g, ∃ hg : g ∈ conjClosure S.V3 H, g ∈ W₁ ∧ modMk hUV g hg ∉ Wm) →
      (∀ g ∈ W₁, ∀ a ∈ K, ∀ b ∈ K.map (MulAut.conj t).toMonoidHom,
        b * (a * g * a⁻¹ * g⁻¹) * b⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ W₀) → False := by
    intro W₀ W₁ hW₀ hW₁ hs
    refine L2Ten.false_of_sum hV₁ hUN hUV Wm hCK hCKt hW₀ hW₁ fun g hg x hx y hy => ?_
    have hy' : (y : G) ∈ K.map (MulAut.conj t).toMonoidHom := by
      rw [hKtsub] at hy
      exact Subgroup.mem_subgroupOf.mp hy
    exact hs g hg x (Subgroup.mem_subgroupOf.mp hx) y hy'
  obtain ⟨I, hV₁I, hIU, Wa, hWa, hirr⟩ := exists_isIrrPlusTildeU hF
  have hFI := factElem hF hIU
  have hIT := isIrrPlusTildeT_of_ambient hF hIU Wa hWa hirr
  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hIT
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hIT
  have hntI := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hIHU : conjClosure I H ≤ conjClosure S.V3 H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    hF.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hWK := hF.tilde_commutator_conjClosure hIU hI
  have hW0 := tildeOf_conjClosure_ne_bot hF hIU hI
  have hV₁IH : fsuV1 T V ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hK₀T : (conjClosure K T ⊔ T).subgroupOf H = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    exact hHK ▸ sup_le_sup_right (le_conjClosure K T) T
  have hUNI : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure _ _
  have hUWI : conjClosure I H ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) :=
    hF.conjClosure_le_normalizer_V₁ hIU
  have hQI : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hV₁ hUNI x = 1 := fun x hx =>
    hF.actH_eq_one_of_mem_pCoreOf hIU hx
  have hntI' : ¬ (conjClosure K T).subgroupOf H ≤ (actH hV₁ hUNI).ker := by
    intro h
    apply hntI
    intro k hk i hi
    have h1 := h (Subgroup.mem_subgroupOf.mpr hk :
      (⟨k, hF.K₀_le_H hk⟩ : ↥H) ∈ (conjClosure K T).subgroupOf H)
    exact (S153M.actE_eq_one_iff hV₁ hUNI hUWI ⟨k, hF.K₀_le_H hk⟩).mp h1 i
      (le_conjClosure I H hi)
  have hrangeI : autOn (tildeOf (fsuV1 T V) (conjClosure K T ⊔ T))
      (tildeOf (fsuV1 T V) (conjClosure I H)) = (actH hV₁ hUNI).range := by
    rw [autOn_tilde_eq_map_actH hV₁ hUNI hF.K₀T_le_H, hK₀T, ← MonoidHom.range_eq_map]
  have hsecI := fun hFF => L2Ten.twoSum_sec hA21 h56 hF hHq hHK htT hKt hK₀eq hcomm hperm hn
    hV₁ hUNI hUWI hQI hntI' hFF
  by_cases ha : tildeOf (fsuV1 T V) (conjClosure I H) =
      tildeOf (fsuV1 T V) ⁅conjClosure S.V3 H, conjClosure K T⁆
  ·
    have hUK : conjClosure S.V3 H ≤ ⁅conjClosure S.V3 H, conjClosure K T⁆ := by
      have hN := A5.le_normalizer_commutator (A := conjClosure S.V3 H) (B := conjClosure K T)
        hUN hF.K₀_normal
      refine conjClosure_le fun h hh x hx => ?_
      have hx' : x ∈ ⁅conjClosure S.V3 H, conjClosure K T⁆ :=
        Subgroup.commutator_mono (le_conjClosure _ _) hℓK (S.V3_le_commutator_V3_L1 hx)
      exact (Subgroup.mem_normalizer_iff.mp (hN hh) x).mp hx'
    have hUI : conjClosure S.V3 H ≤ conjClosure I H := by
      intro g hg
      have h1 : secMk (Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G)) (fsuV1 T V)
          ⟨g, hUV hg⟩ ∈ tildeOf (fsuV1 T V) (conjClosure I H) := by
        rw [ha]
        exact secMk_mem_secImg (A := Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G))
          (B := fsuV1 T V) (X := ⁅conjClosure S.V3 H, conjClosure K T⁆) (x := ⟨g, hUV hg⟩)
          (hUK hg)
      exact (secMk_mem_tildeOf_iff hV₁IH).mp h1
    have hW₁I : ∃ g, ∃ hg : g ∈ conjClosure S.V3 H, g ∈ conjClosure I H ∧
        modMk hUV g hg ∉ Wm := by
      obtain ⟨g, hg, hgm⟩ := hout
      exact ⟨g, hg, hUI hg, hgm⟩
    obtain ⟨-, hFive⟩ := F918_5' hF hHq hne hV₁I hIU Wa hWa hirr hD36 hD37 hD321 hI5 h37 h38
    have h5 := hFive t htT htK
    have hLeq : autIH (fsuV1 T V) I H K = (K.subgroupOf H).map (actH hV₁ hUNI) :=
      autIH_eq_map hF hKH
    have hLt : conjAutSub (actH hV₁ hUNI t') ((K.subgroupOf H).map (actH hV₁ hUNI)) =
        ((K.subgroupOf H).map (MulAut.conj t').toMonoidHom).map (actH hV₁ hUNI) :=
      L2Hat.map_map_conj _ _ _
    have hiso : ∀ {m : ℕ} {p e : ℕ}, IsPSL m p e ↥(autIH (fsuV1 T V) I H K) →
        Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autIH (fsuV1 T V) I H K)) := by
      intro m p e h
      exact nonempty_mulEquiv_quotient_autI hF hIU hsimple
        ((Subgroup.nontrivial_iff_ne_bot _).mp
          (CFSG.LieType.Simplicity.fam_PSL_simplicity _ m p e h).1)
    rcases h5 with ⟨hVtop, -, m, hm, hO4⟩ | ⟨hVtop, -, hL32, -⟩ | h3 | h4
    ·
      have hmI := isPSL_of_autSub_top hVtop hm
      obtain ⟨e⟩ := hiso hmI
      have hmn : m = n := L2Ten.eq_of_isPSL_two_two (isPSL_congr e.symm hmI) hn
      have hO4' := L2Ten.omega4PlusModule_of_autSub_top hVtop hO4
      rw [hmn, hn2] at hO4'
      have hIeq : conjClosure I H = conjClosure S.V3 H := le_antisymm hIHU hUI
      exact hOrth G T L V S hS hhat H hH K hK hne hHeq (hn2 ▸ hn)
        (L2Ten.omega4PlusModule_congr hIeq hO4')
    ·
      have hL32I := isPSL_of_autSub_top hVtop hL32
      obtain ⟨e⟩ := hiso hL32I
      exact not_isPSL_two_two_of_isPSL_three_two hL32I (isPSL_congr e hn)
    ·
      have h3' := h3.2.1
      rw [hLeq, hLt] at h3'
      exact L2Ten.false_of_sum hV₁ hUN hUV Wm hCK hCKt hW₀V hW₁I fun g hg x hx y hy =>
        L2Ten.comm_mem_of_commV_le hV₁ hUNI hUWI h3' hg hx hy
    ·
      have h4' := h4.2.1
      have e : conjAutSub (actH hV₁ hUNI t')⁻¹ (conjAutSub (actH hV₁ hUNI t')
          (autIH (fsuV1 T V) I H K)) = autIH (fsuV1 T V) I H K :=
        L2Hat.map_conj_inv_map_conj _ _
      rw [e, hLeq, hLt] at h4'
      exact L2Ten.false_of_sum hV₁ hUN hUV Wm hCKt hCK hW₀V hW₁I fun g hg x hx y hy =>
        L2Ten.comm_mem_of_commV_le hV₁ hUNI hUWI h4' hg hx hy
  ·
    have hFE : Fact (IsElemAbelian 2 (tildeOf (conjClosure I H) (conjClosure S.V3 H))) :=
      ⟨hF.isElemAbelian_quotient (conjClosure I H)⟩
    have hWNE : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure _ _
    have hUWE : conjClosure S.V3 H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
      HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 hIHU
    have hQE : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWNE hUN x = 1 := fun x hx =>
      S153M.actE_eq_one_of_mem_pCoreOf hF hV₁IH hWNE hUWE hx
    have hntE : ¬ (conjClosure K T).subgroupOf H ≤ (actH hWNE hUN).ker := by
      intro h
      refine S153M.not_forall_comm_of_ne hIHU hWK ha ?_
      intro k hk u hu
      have h1 := h (Subgroup.mem_subgroupOf.mpr hk :
        (⟨k, hF.K₀_le_H hk⟩ : ↥H) ∈ (conjClosure K T).subgroupOf H)
      exact (S153M.actE_eq_one_iff hWNE hUN hUWE ⟨k, hF.K₀_le_H hk⟩).mp h1 u hu
    have hrangeE : autOn (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
        (tildeOf (conjClosure I H) (conjClosure S.V3 H)) = (actH hWNE hUN).range := by
      rw [autOn_tilde_eq_map_actH hWNE hUN hF.K₀T_le_H, hK₀T, ← MonoidHom.range_eq_map]
    have hsecE := fun hFF => L2Ten.twoSum_sec hA21 h56 hF hHq hHK htT hKt hK₀eq hcomm hperm hn
      hWNE hUN hUWE hQE hntE hFF
    rcases hF.F918_6 hV₁IH hIHU hIHN hW0 hWK with ha' | ⟨hb1, hb2⟩ | hc1 | hc2
    · exact ha ha'
    ·
      have hb1' : IsFFModule (actH hV₁ hUNI).range := by
        have h1 : IsFFModule (autOn (tildeOf (fsuV1 T V) (conjClosure K T ⊔ T))
            (tildeOf (fsuV1 T V) (conjClosure I H))) := hb1
        rwa [hrangeI] at h1
      have hb2' : IsFFModule (actH hWNE hUN).range := by
        have h1 : IsFFModule (autOn (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
            (tildeOf (conjClosure I H) (conjClosure S.V3 H))) := hb2
        rwa [hrangeE] at h1
      by_cases hIWm : ∀ g (hg : g ∈ conjClosure S.V3 H), g ∈ conjClosure I H →
          modMk hUV g hg ∈ Wm
      · obtain ⟨g, hg, hgm⟩ := hout
        exact hfin hIWm ⟨g, hg, hg, hgm⟩ (hsecE hb2').1
      · push Not at hIWm
        obtain ⟨g, hg, hgI, hgm⟩ := hIWm
        exact hfin hW₀V ⟨g, hg, hgI, hgm⟩ (hsecI hb1').1
    ·
      have h1 : IsStrongFFModule (autOn (tildeOf (fsuV1 T V) (conjClosure K T ⊔ T))
          (tildeOf (fsuV1 T V) (conjClosure I H))) := hc1
      rw [hrangeI] at h1
      exact (hsecI (L2Ten.isFFModule_of_isStrongFFModule h1)).2 h1
    ·
      have h1 : IsStrongFFModule (autOn (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
          (tildeOf (conjClosure I H) (conjClosure S.V3 H))) := hc2
      rw [hrangeE] at h1
      exact (hsecE (L2Ten.isFFModule_of_isStrongFFModule h1)).2 h1


end CFSG.Quasithin.H13.A6
