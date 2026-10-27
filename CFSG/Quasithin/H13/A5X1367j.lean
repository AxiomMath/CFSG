module

public import CFSG.Quasithin.H13.A5X1367i
public import CFSG.Quasithin.EmptyFaithful.SzN17Dig
public import CFSG.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem two_pow_of_TvS {s : MulAut ↥S.Uv} (hs : s ∈ autOn S.Tv S.Uv) :
    ∃ k : ℕ, s ^ 2 ^ k = 1 := by
  obtain ⟨⟨s₀, hs₀N⟩, hs₀, rfl⟩ := hs
  obtain ⟨k, hk⟩ := S.isPGroup_T ⟨s₀, (Subgroup.mem_subgroupOf.mp hs₀).1⟩
  refine ⟨k, ?_⟩
  have : (⟨s₀, hs₀N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  rw [← map_pow, this, map_one]

theorem exists_inv_TvS (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    {J G₁ : Subgroup (MulAut ↥S.Uv)}
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv)))
    (hG₁J : G₁ ≤ J) (hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥S.Uv)))
    (h6 : Nat.card ↥G₁ = 6) : ∃ s ∈ autOn S.Tv S.Uv ⊓ G₁, s ≠ 1 := by
  have hsylJ := A4.isSylowTwoOf_inf_normal (S.isSylowTwoOf_TvS h1222 h517) hJG hGJ
  have hsyl₁ := A4.isSylowTwoOf_inf_normal hsylJ hG₁J hJG₁
  by_contra hcon
  push Not at hcon
  have hbot : autOn S.Tv S.Uv ⊓ J ⊓ G₁ = ⊥ :=
    eq_bot_iff.mpr fun x hx => hcon x ⟨hx.1.1, hx.2⟩
  have h : ¬ 2 ∣ (autOn S.Tv S.Uv ⊓ J ⊓ G₁).relIndex G₁ := hsyl₁.2.2
  rw [hbot, Subgroup.relIndex_bot_left, h6] at h
  exact h (by norm_num)

variable [IsMulCommutative ↥S.Uv]

theorem false_of_ds3_noswap (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hVv : ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G))
    {J G₁ G₂ : Subgroup (MulAut ↥S.Uv)} {W₁ W₂ : Subgroup ↥S.Uv} {y₁ y₂ : MulAut ↥S.Uv}
    (hD : DS3 J G₁ G₂ W₁ W₂ y₁ y₂)
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv)))
    (hnorm : ∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv,
      g * y₁ * g⁻¹ = y₁ ∨ g * y₁ * g⁻¹ = y₁⁻¹) : False := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have hU2 : ∀ u : ↥S.Uv, u * u = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  obtain ⟨hEW, hcard, hker⟩ := hD.struct₁ hU2
  have hy3 : y₁ ^ 3 = 1 := by rw [← hD.y₁ord]; exact pow_orderOf_eq_one y₁
  have hy1 : y₁ ≠ 1 := fun h => by
    have h3 := hD.y₁ord
    rw [h, orderOf_one] at h3
    omega
  have hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥S.Uv)) := by
    intro g hg
    have h1 := (SzN17.normal_of_commuting hD.sup hD.comm).1 g hg
    refine B6.mem_normalizer_of_forall_mem (h1) fun x hx => ?_
    have := (SzN17.normal_of_commuting hD.sup hD.comm).1 g⁻¹ (J.inv_mem hg) x hx
    simpa using this
  obtain ⟨s, ⟨hsT, hsG₁⟩, hs1⟩ :=
    S.exists_inv_TvS h1222 h517 hJG hGJ hD.G₁_le hJG₁ hD.card₁
  have hsW : ∀ w ∈ (threePhi y₁).ker, s w = w := by
    rw [hker]
    exact hD.trivial_W₂ hU2 hsG₁ (S.two_pow_of_TvS hsT)
  apply hVv
  refine S.le_normalizer_Vv_of_three hUe (Y := Subgroup.zpowers y₁)
    ((Subgroup.zpowers_le).mpr (hJG (hD.G₁_le hD.y₁mem))) ?_ ?_ hcard ?_
    (three_range_inf_ker hU2 hy3) ?_ ?_ ?_ ?_ hsT hsW ?_
  · intro g hg
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow]
      rcases hnorm g hg with h | h <;> rw [h]
      · exact Subgroup.zpow_mem_zpowers _ _
      · rw [inv_zpow']
        exact Subgroup.zpow_mem_zpowers _ _
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hg' := Subgroup.inv_mem _ hg
      have e : g⁻¹ * y₁ ^ k * g = g⁻¹ * y₁ ^ k * g⁻¹⁻¹ := by rw [inv_inv]
      rw [e, ← conj_zpow]
      rcases hnorm g⁻¹ hg' with h | h <;> rw [h]
      · exact Subgroup.zpow_mem_zpowers _ _
      · rw [inv_zpow']
        exact Subgroup.zpow_mem_zpowers _ _
  · intro h
    apply hy1
    have := Subgroup.mem_zpowers y₁
    rw [h, Subgroup.mem_bot] at this
    exact this
  · intro u
    obtain ⟨h1, h2⟩ := three_decomp hU2 hy3 u
    exact ⟨_, ⟨y₁ u, rfl⟩, _, h2, h1.symm⟩
  · intro y hy w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hw' : y₁ w = w := mem_ker_threePhi.mp hw
    have hk : ∀ n : ℕ, (y₁ ^ n) w = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hw', ih]
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]; exact hk n
    · rw [zpow_neg, zpow_natCast]
      conv_lhs => rw [← hk n]
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  · intro u hu hfix
    exact three_range_fix hU2 hy3 hu (hfix y₁ (Subgroup.mem_zpowers y₁))
  · intro g hg u hu
    exact three_range_apply hU2 (hnorm g hg) hu
  · intro g hg w hw
    exact three_ker_apply (hnorm g hg) hw
  · by_contra hcon
    push Not at hcon
    apply hs1
    ext u
    obtain ⟨h1, h2⟩ := three_decomp hU2 hy3 u
    rw [← h1, map_mul, hcon _ ⟨y₁ u, rfl⟩, hsW _ h2, MulAut.one_apply]

omit [IsMulCommutative ↥S.Uv] in
theorem conj_mem_LvS {t d : MulAut ↥S.Uv} (ht : t ∈ autOn S.Tv S.Uv) (hd : d ∈ autOn S.Lv S.Uv) :
    t * d * t⁻¹ ∈ autOn S.Lv S.Uv := by
  obtain ⟨⟨t₀, ht₀N⟩, ht₀, rfl⟩ := ht
  obtain ⟨⟨d₀, hd₀N⟩, hd₀, rfl⟩ := hd
  have ht₀T : t₀ ∈ S.Tv := Subgroup.mem_subgroupOf.mp ht₀
  have hd₀L : d₀ ∈ S.Lv := Subgroup.mem_subgroupOf.mp hd₀
  have hm : t₀ * d₀ * t₀⁻¹ ∈ S.Lv :=
    (Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv ht₀T) d₀).mp hd₀L
  have hmN : t₀ * d₀ * t₀⁻¹ ∈ Subgroup.normalizer (S.Uv : Set G) :=
    S.Gv_le_normalizer_Uv (S.Lv_le_Gv hm)
  refine ⟨⟨_, hmN⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [IsMulCommutative ↥S.Uv] in
theorem eq_or_eq_inv_of_LvS {d₁ d₂ : MulAut ↥S.Uv} (hd₁ : d₁ ∈ autOn S.Lv S.Uv)
    (hd₂ : d₂ ∈ autOn S.Lv S.Uv) (h₁3 : d₁ ^ 3 = 1) (h₂3 : d₂ ^ 3 = 1) (h₁1 : d₁ ≠ 1)
    (h₂1 : d₂ ≠ 1) (hc : d₁ * d₂ = d₂ * d₁) : d₁ = d₂ ∨ d₁ = d₂⁻¹ := by
  have key : ∀ {e : MulAut ↥S.Uv} (l : G) (hlN : l ∈ Subgroup.normalizer (S.Uv : Set G))
      (hl : l ∈ S.Lv) (hlV : l ∈ Subgroup.normalizer (V : Set G)),
      conjAct S.Uv ⟨l, hlN⟩ = e → e ^ 3 = 1 → S.frame.ρ ⟨l, hlV⟩ = 1 → e = 1 := by
    intro e l hlN hl hlV hle he3 hρ
    obtain ⟨k, hk⟩ := S.two_pow_of_Lv_of_rho ⟨l, hlV⟩ hl hρ
    have hek : e ^ 2 ^ k = 1 := by
      rw [← hle, ← map_pow]
      have : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h1 : orderOf e ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he3) (orderOf_dvd_of_pow_eq_one hek)
    have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  obtain ⟨⟨l₁, hl₁N⟩, hl₁L, rfl⟩ := hd₁
  obtain ⟨⟨l₂, hl₂N⟩, hl₂L, rfl⟩ := hd₂
  have hl₁ : l₁ ∈ S.Lv := Subgroup.mem_subgroupOf.mp hl₁L
  have hl₂ : l₂ ∈ S.Lv := Subgroup.mem_subgroupOf.mp hl₂L
  have hl₁V : l₁ ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (oTwoRes_le _ hl₁).1
  have hl₂V : l₂ ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (oTwoRes_le _ hl₂).1
  have hρ₁ : S.frame.ρ ⟨l₁, hl₁V⟩ ≠ 1 := fun h => h₁1 (key l₁ hl₁N hl₁ hl₁V rfl h₁3 h)
  have hρ₂ : S.frame.ρ ⟨l₂, hl₂V⟩ ≠ 1 := fun h => h₂1 (key l₂ hl₂N hl₂ hl₂V rfl h₂3 h)
  have hcyc : ∀ {a b : Equiv.Perm (Fin 5)}, (a = c234 ∨ a = c234⁻¹) → (b = c234 ∨ b = c234⁻¹) →
      a * b⁻¹ = 1 ∨ a * b = 1 := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · left; exact mul_inv_cancel _
    · right; exact mul_inv_cancel _
    · right; exact inv_mul_cancel _
    · left; rw [inv_inv]; exact inv_mul_cancel _
  have h₁c : S.frame.ρ ⟨l₁, hl₁V⟩ = c234 ∨ S.frame.ρ ⟨l₁, hl₁V⟩ = c234⁻¹ := by
    rcases S.rho_Lv_cases ⟨l₁, hl₁V⟩ hl₁ with h | h | h
    · exact absurd h hρ₁
    · exact Or.inl h
    · exact Or.inr h
  have h₂c : S.frame.ρ ⟨l₂, hl₂V⟩ = c234 ∨ S.frame.ρ ⟨l₂, hl₂V⟩ = c234⁻¹ := by
    rcases S.rho_Lv_cases ⟨l₂, hl₂V⟩ hl₂ with h | h | h
    · exact absurd h hρ₂
    · exact Or.inl h
    · exact Or.inr h
  set D₁ := conjAct S.Uv ⟨l₁, hl₁N⟩ with hD₁
  set D₂ := conjAct S.Uv ⟨l₂, hl₂N⟩ with hD₂
  rcases hcyc h₁c h₂c with h | h
  ·
    left
    have hm : l₁ * l₂⁻¹ ∈ S.Lv := S.Lv.mul_mem hl₁ (S.Lv.inv_mem hl₂)
    have hmN : l₁ * l₂⁻¹ ∈ Subgroup.normalizer (S.Uv : Set G) :=
      Subgroup.mul_mem _ hl₁N (Subgroup.inv_mem _ hl₂N)
    have hmV : l₁ * l₂⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ hl₁V (Subgroup.inv_mem _ hl₂V)
    have hρm : S.frame.ρ ⟨l₁ * l₂⁻¹, hmV⟩ = 1 := by
      have : (⟨l₁ * l₂⁻¹, hmV⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨l₁, hl₁V⟩ * ⟨l₂, hl₂V⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, h]
    have hDm : conjAct S.Uv ⟨l₁ * l₂⁻¹, hmN⟩ = D₁ * D₂⁻¹ := by
      rw [hD₁, hD₂, ← map_inv, ← map_mul]
      rfl
    have h3 : (D₁ * D₂⁻¹) ^ 3 = 1 := by
      rw [(Commute.mul_pow (Commute.inv_right hc) 3), h₁3, inv_pow, h₂3, inv_one, one_mul]
    have := key (l₁ * l₂⁻¹) hmN hm hmV hDm h3 hρm
    exact mul_inv_eq_one.mp this
  · right
    have hm : l₁ * l₂ ∈ S.Lv := S.Lv.mul_mem hl₁ hl₂
    have hmN : l₁ * l₂ ∈ Subgroup.normalizer (S.Uv : Set G) := Subgroup.mul_mem _ hl₁N hl₂N
    have hmV : l₁ * l₂ ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hl₁V hl₂V
    have hρm : S.frame.ρ ⟨l₁ * l₂, hmV⟩ = 1 := by
      have : (⟨l₁ * l₂, hmV⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨l₁, hl₁V⟩ * ⟨l₂, hl₂V⟩ :=
        rfl
      rw [this, map_mul, h]
    have hDm : conjAct S.Uv ⟨l₁ * l₂, hmN⟩ = D₁ * D₂ := by
      rw [hD₁, hD₂, ← map_mul]
      rfl
    have h3 : (D₁ * D₂) ^ 3 = 1 := by
      rw [(Commute.mul_pow hc 3), h₁3, h₂3, one_mul]
    have := key (l₁ * l₂) hmN hm hmV hDm h3 hρm
    exact eq_inv_of_mul_eq_one_left this

theorem zU_mem_of_trivial (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {J G₁ G₂ : Subgroup (MulAut ↥S.Uv)} {W₁ W₂ : Subgroup ↥S.Uv} {y₁ y₂ : MulAut ↥S.Uv}
    (hD : DS3 J G₁ G₂ W₁ W₂ y₁ y₂)
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (l₀ : ↥(Subgroup.normalizer (V : Set G)))
    (hl₀σ : S.frame.ρ l₀ = c234 ∨ S.frame.ρ l₀ = c234⁻¹)
    (hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G))
    (hfix : DS3.FixY y₁ (conjAct S.Uv ⟨l₀, hl₀N⟩))
    (htriv : ∀ e ∈ (threePhi y₁).range, conjAct S.Uv ⟨l₀, hl₀N⟩ e = e) : S.zU ∈ W₂ := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have hU2 : ∀ u : ↥S.Uv, u * u = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  obtain ⟨-, -, hker⟩ := hD.struct₁ hU2
  have hy3 : y₁ ^ 3 = 1 := by rw [← hD.y₁ord]; exact pow_orderOf_eq_one y₁
  set lS := conjAct S.Uv ⟨l₀, hl₀N⟩ with hlS
  have hfixinv : DS3.FixY y₁ lS⁻¹ := by
    unfold DS3.FixY at hfix ⊢
    rcases hfix with h | h
    · left
      have h' : y₁ = lS⁻¹ * y₁ * lS := by
        calc y₁ = lS⁻¹ * (lS * y₁ * lS⁻¹) * lS := by group
          _ = lS⁻¹ * y₁ * lS := by rw [h]
      rw [inv_inv]; exact h'.symm
    · right
      have h' : y₁⁻¹ = lS⁻¹ * y₁ * lS := by
        calc y₁⁻¹ = lS⁻¹ * (lS * y₁ * lS⁻¹)⁻¹ * lS := by group
          _ = lS⁻¹ * y₁⁻¹⁻¹ * lS := by rw [h]
          _ = lS⁻¹ * y₁ * lS := by rw [inv_inv]
      rw [inv_inv]; exact h'.symm
  have hlinv : ∀ e ∈ (threePhi y₁).range, lS⁻¹ e = e := fun e he => by
    conv_lhs => rw [← htriv e he]
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hv := S.vU_eq_mul_conjAct l₀ hl₀σ hl₀N
  rw [← hlS] at hv
  obtain ⟨hz1, hz2⟩ := three_decomp hU2 hy3 S.zU
  obtain ⟨e₁, he₁E, c₁, hz2', hzdec⟩ : ∃ e₁ ∈ (threePhi y₁).range, ∃ c₁ ∈ (threePhi y₁).ker,
      S.zU = e₁ * c₁ := ⟨_, ⟨y₁ S.zU, rfl⟩, _, hz2, hz1.symm⟩
  clear hz1 hz2
  rename_i hz2
  have hz2 := hz2'
  have hw' : c₁ * lS c₁ * lS⁻¹ c₁ ∈ (threePhi y₁).ker :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hz2 (three_ker_apply hfix hz2))
      (three_ker_apply hfixinv hz2)
  have hvdec : S.vU = e₁ * (c₁ * lS c₁ * lS⁻¹ c₁) := by
    have hcomm : ∀ a b : ↥S.Uv, a * b = b * a := fun a b => hUe.1.is_comm.comm a b
    rw [hv, hzdec, map_mul, map_mul, htriv e₁ he₁E, hlinv e₁ he₁E]
    calc e₁ * c₁ * (e₁ * lS c₁) * (e₁ * lS⁻¹ c₁)
        = e₁ * (c₁ * e₁) * lS c₁ * (e₁ * lS⁻¹ c₁) := by group
      _ = e₁ * (e₁ * c₁) * lS c₁ * (e₁ * lS⁻¹ c₁) := by rw [hcomm c₁ e₁]
      _ = (e₁ * e₁) * (c₁ * lS c₁ * e₁) * lS⁻¹ c₁ := by group
      _ = (e₁ * e₁) * (e₁ * (c₁ * lS c₁)) * lS⁻¹ c₁ := by rw [hcomm (c₁ * lS c₁) e₁]
      _ = e₁ * (c₁ * lS c₁ * lS⁻¹ c₁) := by rw [hU2, one_mul]; group
  have hvW : S.vU ∈ (threePhi y₁).ker :=
    mem_ker_threePhi.mpr (S.apply_vU (hJG (hD.G₁_le hD.y₁mem)))
  have h1 := decomp_unique (three_range_inf_ker hU2 hy3) he₁E hw' (Subgroup.one_mem _) hvW
    (by rw [one_mul, ← hvdec])
  rw [hzdec, h1.1, one_mul, ← hker]
  exact hz2

theorem false_of_ds3_swap (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {J G₁ G₂ : Subgroup (MulAut ↥S.Uv)} {W₁ W₂ : Subgroup ↥S.Uv} {y₁ y₂ : MulAut ↥S.Uv}
    (hD : DS3 J G₁ G₂ W₁ W₂ y₁ y₂)
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv))) (hJ1 : J ≠ ⊥)
    {t : MulAut ↥S.Uv} (ht : t ∈ autOn S.Tv S.Uv)
    (hts : t * y₁ * t⁻¹ = y₂ ∨ t * y₁ * t⁻¹ = y₂⁻¹) : False := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have hU2 : ∀ u : ↥S.Uv, u * u = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  set GS := autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv with hGS
  obtain ⟨hE₁W, hE₁c, hker₁⟩ := hD.struct₁ hU2
  obtain ⟨hE₂W, hE₂c, hker₂⟩ := hD.symm.struct₁ hU2
  have hy₁3 : y₁ ^ 3 = 1 := by rw [← hD.y₁ord]; exact pow_orderOf_eq_one y₁
  have htG : t ∈ GS := S.autOn_le_GvS S.Tv_le_Gv ht
  have htJ : t ∈ Subgroup.normalizer (J : Set (MulAut ↥S.Uv)) := hGJ htG
  have hts' : t⁻¹ * y₂ * t⁻¹⁻¹ = y₁ ∨ t⁻¹ * y₂ * t⁻¹⁻¹ = y₁⁻¹ := by
    rw [inv_inv]
    rcases hts with h | h
    · left
      calc t⁻¹ * y₂ * t = t⁻¹ * (t * y₁ * t⁻¹) * t := by rw [h]
        _ = y₁ := by group
    · right
      calc t⁻¹ * y₂ * t = t⁻¹ * (t * y₁ * t⁻¹)⁻¹ * t := by rw [h, inv_inv]
        _ = y₁⁻¹ := by group
  have htE : ∀ e ∈ (threePhi y₁).range, t e ∈ (threePhi y₂).range := by
    intro e he
    have h := three_range_conj (g := t) he
    rcases hts with h' | h' <;> rw [h'] at h
    · exact h
    · exact three_range_inv h
  have htW : ∀ w ∈ W₂, t w ∈ W₁ := by
    intro w hw
    rw [← hker₁] at hw
    rw [← hker₂]
    have h := three_ker_conj (g := t) hw
    rcases hts with h' | h' <;> rw [h'] at h
    · exact h
    · exact three_ker_inv h
  have htE' : ∀ e ∈ (threePhi y₂).range, t⁻¹ e ∈ (threePhi y₁).range := by
    intro e he
    have h := three_range_conj (g := t⁻¹) he
    rcases hts' with h' | h' <;> rw [h'] at h
    · exact h
    · exact three_range_inv h
  obtain ⟨l₀, hl₀Lv, hl₀odd, hl₀σ⟩ := S.exists_Lv_c234_odd
  have hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G) :=
    S.Gv_le_normalizer_Uv (S.Lv_le_Gv hl₀Lv)
  have hoddS : ∀ (m : G) (hmN : m ∈ Subgroup.normalizer (S.Uv : Set G)),
      Odd (orderOf m) → Odd (orderOf (conjAct S.Uv ⟨m, hmN⟩)) := by
    intro m hmN hm
    refine Odd.of_dvd_nat hm ?_
    have h1 := orderOf_map_dvd (conjAct S.Uv)
      (⟨m, hmN⟩ : ↥(Subgroup.normalizer (S.Uv : Set G)))
    rwa [Subgroup.orderOf_mk] at h1
  have hGSl : ∀ (m : G) (hmN : m ∈ Subgroup.normalizer (S.Uv : Set G)), m ∈ S.Lv →
      conjAct S.Uv ⟨m, hmN⟩ ∈ GS := fun m hmN hm =>
    S.autOn_le_GvS S.Lv_le_Gv ⟨⟨m, hmN⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  have hfix₁ := hD.fixY_of_odd (hGJ (hGSl _ hl₀N hl₀Lv)) (hoddS _ hl₀N hl₀odd)
  have hfix₂ := hD.symm.fixY_of_odd (hGJ (hGSl _ hl₀N hl₀Lv)) (hoddS _ hl₀N hl₀odd)
  have hlE : (∃ e ∈ (threePhi y₁).range, conjAct S.Uv ⟨l₀, hl₀N⟩ e ≠ e) ∨
      (∃ e ∈ (threePhi y₂).range, conjAct S.Uv ⟨l₀, hl₀N⟩ e ≠ e) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hz₂ := S.zU_mem_of_trivial h1222 h517 hF hD hJG l₀ hl₀σ hl₀N hfix₁ h1
    have hz₁ := S.zU_mem_of_trivial h1222 h517 hF hD.symm hJG l₀ hl₀σ hl₀N hfix₂ h2
    have hzC : S.zU ∈ fixV J := hD.Winf ▸ ⟨hz₁, hz₂⟩
    obtain ⟨x, hxJ, hxz⟩ := S.exists_apply_ne_zU_of_normal hGJ hJ1
    exact hxz (hzC x hxJ)
  obtain ⟨l', hl'Lv, hl'odd, hl'N, hl'E⟩ : ∃ l' : ↥(Subgroup.normalizer (V : Set G)),
      (l' : G) ∈ S.Lv ∧ Odd (orderOf (l' : G)) ∧ ∃ hl'N : (l' : G) ∈ Subgroup.normalizer
        (S.Uv : Set G), ∃ e ∈ (threePhi y₁).range, conjAct S.Uv ⟨l', hl'N⟩ e ≠ e := by
    rcases hlE with h1 | ⟨e₂, he₂, hle₂⟩
    · exact ⟨l₀, hl₀Lv, hl₀odd, hl₀N, h1⟩
    · obtain ⟨⟨t₀, ht₀N⟩, ht₀, rfl⟩ := ht
      have ht₀T : t₀ ∈ S.Tv := Subgroup.mem_subgroupOf.mp ht₀
      have ht₀V : t₀ ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le ht₀T.1
      set m : ↥(Subgroup.normalizer (V : Set G)) := ⟨t₀, ht₀V⟩⁻¹ * l₀ * ⟨t₀, ht₀V⟩ with hm
      have hmG : (m : G) = t₀⁻¹ * l₀ * t₀ := rfl
      have hmLv : (m : G) ∈ S.Lv := by
        rw [hmG]
        have := (Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv (S.Tv.inv_mem ht₀T))
          l₀).mp hl₀Lv
        simpa using this
      have hmodd : Odd (orderOf (m : G)) := by
        rw [hmG, show t₀⁻¹ * (l₀ : G) * t₀ = t₀⁻¹ * l₀ * t₀⁻¹⁻¹ by rw [inv_inv], orderOf_conj']
        exact hl₀odd
      have hmN : (m : G) ∈ Subgroup.normalizer (S.Uv : Set G) :=
        S.Gv_le_normalizer_Uv (S.Lv_le_Gv hmLv)
      have hconjm : conjAct S.Uv ⟨m, hmN⟩ =
          (conjAct S.Uv ⟨t₀, ht₀N⟩)⁻¹ * conjAct S.Uv ⟨l₀, hl₀N⟩ * conjAct S.Uv ⟨t₀, ht₀N⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      refine ⟨m, hmLv, hmodd, hmN, (conjAct S.Uv ⟨t₀, ht₀N⟩)⁻¹ e₂, htE' e₂ he₂, ?_⟩
      rw [hconjm]
      simp only [MulAut.mul_apply]
      intro h
      apply hle₂
      have hh : ∀ u, conjAct S.Uv ⟨t₀, ht₀N⟩ ((conjAct S.Uv ⟨t₀, ht₀N⟩)⁻¹ u) = u := fun u => by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      have := congrArg (conjAct S.Uv ⟨t₀, ht₀N⟩) h
      rwa [hh, hh] at this
  set lS := conjAct S.Uv ⟨l', hl'N⟩ with hlS
  have hfix' := hD.fixY_of_odd (hGJ (hGSl _ hl'N hl'Lv)) (hoddS _ hl'N hl'odd)
  have hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥S.Uv)) := by
    intro g hg
    refine B6.mem_normalizer_of_forall_mem ((SzN17.normal_of_commuting hD.sup hD.comm).1 g hg)
      fun x hx => ?_
    have := (SzN17.normal_of_commuting hD.sup hD.comm).1 g⁻¹ (J.inv_mem hg) x hx
    simpa using this
  obtain ⟨s, ⟨hsT, hsG₁⟩, hs1⟩ :=
    S.exists_inv_TvS h1222 h517 hJG hGJ hD.G₁_le hJG₁ hD.card₁
  have hsW : ∀ w ∈ W₂, s w = w := hD.trivial_W₂ hU2 hsG₁ (S.two_pow_of_TvS hsT)
  have hsfix : DS3.FixY y₁ s := by
    have h := hD.zpowers_normal₁ s (hD.G₁_le hsG₁)
    refine eq_or_eq_inv_of_mem_zpowers hD.y₁ord h ?_
    intro h1
    apply hD.y₁_ne_one
    have := congrArg (fun x => s⁻¹ * x * s) h1
    simpa [mul_assoc] using this
  have hdec : ∀ u : ↥S.Uv, ∃ a ∈ (threePhi y₁).range, ∃ w ∈ W₂, u = a * w := by
    intro u
    obtain ⟨h1, h2⟩ := three_decomp hU2 hy₁3 u
    exact ⟨_, ⟨y₁ u, rfl⟩, _, hker₁ ▸ h2, h1.symm⟩
  have hsU : ∃ u ∈ (threePhi y₁).range, s u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hs1
    ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    rw [map_mul, hcon a ha, hsW w hw, MulAut.one_apply]
  obtain ⟨d₁, hd₁L, hd₁W, hd₁E, hd₁3, hd₁1⟩ := S.exists_d_of_three hUe hE₁c hdec l' hl'Lv hl'odd
    hl'N (fun u hu => three_range_apply hU2 hfix' hu)
    (fun w hw => by
      rw [← hker₁] at hw ⊢
      exact three_ker_apply hfix' hw) hl'E hsT
    (fun u hu => three_range_apply hU2 hsfix hu) hsW hsU
  set d₂ := t * d₁ * t⁻¹ with hd₂
  have hd₂L : d₂ ∈ autOn S.Lv S.Uv := S.conj_mem_LvS ht hd₁L
  have htt : ∀ u, t (t⁻¹ u) = u := fun u => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have htW' : ∀ w ∈ W₁, t⁻¹ w ∈ W₂ := by
    intro w hw
    rw [← hker₂] at hw
    rw [← hker₁]
    have h := three_ker_conj (g := t⁻¹) hw
    rcases hts' with h' | h' <;> rw [h'] at h
    · exact h
    · exact three_ker_inv h
  have hd₂W : ∀ w ∈ W₁, d₂ w = w := by
    intro w hw
    rw [hd₂]
    simp only [MulAut.mul_apply]
    rw [hd₁W _ (htW' w hw), htt]
  have hd₂3 : d₂ ^ 3 = 1 := by
    rw [hd₂, conj_pow, hd₁3]
    group
  have hd₂1 : d₂ ≠ 1 := by
    intro h
    apply hd₁1
    have := congrArg (fun x => t⁻¹ * x * t) h
    simpa [hd₂, mul_assoc] using this
  have hc : d₁ * d₂ = d₂ * d₁ := by
    ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    have hy₂3 : y₂ ^ 3 = 1 := by rw [← hD.y₂ord]; exact pow_orderOf_eq_one y₂
    obtain ⟨h1, h2⟩ := three_decomp hU2 hy₂3 w
    set e₂ := threePhi y₂ (y₂ w) with he₂
    set c := w * y₂ w * y₂ (y₂ w) with hcdef
    have he₂E : e₂ ∈ (threePhi y₂).range := ⟨_, rfl⟩
    have hcW₁ : c ∈ W₁ := by rw [← hker₂]; exact h2
    have hcW₂ : c ∈ W₂ := by
      have hy₂J : y₂ ∈ J := hD.G₂_le hD.y₂mem
      exact W₂.mul_mem (W₂.mul_mem hw (hD.inv₂ y₂ hy₂J w hw))
        (hD.inv₂ y₂ hy₂J _ (hD.inv₂ y₂ hy₂J w hw))
    have haW₁ : a ∈ W₁ := hE₁W ha
    have hd₁a : d₁ a ∈ W₁ := by
      rw [hd₁E a ha]
      exact hE₁W (three_range_apply hU2 hfix' ha)
    have hd₂e : d₂ e₂ ∈ W₂ := by
      rw [hd₂]
      simp only [MulAut.mul_apply]
      have h3 : t⁻¹ e₂ ∈ (threePhi y₁).range := htE' e₂ he₂E
      rw [hd₁E _ h3]
      exact hE₂W (htE _ (three_range_apply hU2 hfix' h3))
    have he₂W₂ : e₂ ∈ W₂ := hE₂W he₂E
    rw [← h1]
    simp only [MulAut.mul_apply, map_mul, hd₂W a haW₁, hd₂W c hcW₁, hd₁W _ hd₂e, hd₁W c hcW₂,
      hd₁W e₂ he₂W₂, hd₂W _ hd₁a]
  rcases S.eq_or_eq_inv_of_LvS hd₁L hd₂L hd₁3 hd₂3 hd₁1 hd₂1 hc with h | h
  · obtain ⟨e, he, hle⟩ := hl'E
    apply hle
    rw [← hd₁E e he, h, hd₂W e (hE₁W he)]
  · obtain ⟨e, he, hle⟩ := hl'E
    apply hle
    rw [← hd₁E e he, h]
    have := hd₂W e (hE₁W he)
    conv_lhs => rw [← this]
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

end Setting

end CFSG.Quasithin.H13.A5
