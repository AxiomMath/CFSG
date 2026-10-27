module

public import CFSG.Quasithin.H13.U3S13472A
public import CFSG.Quasithin.H13.U3S1347P4G

public section

namespace CFSG.Quasithin.H13.U3.P2

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure Data2 (S : A6.Setting134 G T L V) (H₁ H₂ : Subgroup G) where
  K₀ : Subgroup G
  hyp : Hyp1347 T H₁ H₂
  hH₀ : InH T (H₁ ⊔ H₂)
  hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G)
  hsup : H₁ ⊔ H₂ = K₀ ⊔ T
  hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂)
  hmax : quasithinIsMaximalLocal T K₀
  hK : quasithinO2QuotientIso K₀ SL3.S
  hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G)
  ψ : ↥(H₁ ⊔ H₂) →* SL3.S
  hψ : Function.Surjective ψ
  hker : ψ.ker = Open.pCore 2 ↥(H₁ ⊔ H₂)
  hTψ : (T.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.P0
  hKψ : (K₀.subgroupOf (H₁ ⊔ H₂)).map ψ = ⊤
  hcent : (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂)
  σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)
  hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
    ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹
  Hp : Subgroup G
  Hl : Subgroup G
  hHp : Hp ≤ H₁ ⊔ H₂
  hHl : Hl ≤ H₁ ⊔ H₂
  hpX : (Hp.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1
  hlX : (Hl.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2
  x : ↥(v0Of T H₁ H₂)
  y : ↥(v0Of T H₁ H₂)
  hxp : (x : G) ∈ centralizer (Hp : Set G)
  hyl : (y : G) ∈ centralizer (Hl : Set G)
  hxnl : (x : G) ∉ centralizer (Hl : Set G)
  hynp : (y : G) ∉ centralizer (Hp : Set G)
  hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x ∨ z = y ∨ z = (x : G) * y
  hxZ : (x : G) ∈ quasithinOmegaOneCenter T
  hyZ : (y : G) ∈ quasithinOmegaOneCenter T

theorem exists_data2 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (h1345 : NQS134.Stmt13_4_5) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hii : Concl1347ii T H₁ H₂) :
    Nonempty (Data2 S H₁ H₂) := by
  obtain ⟨hH₀, hH₀M, -, hZsup, hZinf, hc₁, hc₂⟩ :=
    s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨K₀, hsup, hK₀, hmax, -, hK, -, -⟩ := hii
  have hns := s1347_not_solvable_of_cComp hK₀
  have hK₀' : K₀ ∈ cComp (H₁ ⊔ H₂) := hK₀
  obtain ⟨-, hall⟩ := h1345 G T L V S (H₁ ⊔ H₂) hH₀ hH₀M hns
  obtain ⟨-, hN, -⟩ := hall K₀ hK₀'
  have hKH := le_of_mem_cComp hK₀'
  have hiso₀ := s1347_quotIso_H0 S h hN hK hsup
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  obtain ⟨ψ, hψ, hker, hTψ⟩ := I51.exists_model_hom hiso₀ hsyl₀ SL3.P0_sylow.1 SL3.P0_sylow.2
  have hcent := s1347_centralizer_eq S h hH₀ hiso₀
  have hKψ := s1347_map_K0 hψ hker hKH hN hK
  obtain ⟨σ, hσ⟩ := s1347_exists_action S h hH₀ hψ hker
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hP₁ := s1347_map_parabolic hsyl₀ hker hTψ le_sup_left h.inH₁.1 h3₁
  have hP₂ := s1347_map_parabolic hsyl₀ hker hTψ le_sup_right h.inH₂.1 h3₂
  have hne := s1347_map_ne hsyl₀ hker le_sup_left le_sup_right h.inH₁.1 h.inH₂.1 h.ne
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hc₁
  obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_card_two hc₂
  have hZ := s1347_Z_eq hZsup hc₁ hc₂ hu hu1 hv hv1
  have huZ : u ∈ quasithinOmegaOneCenter T := (mem_inf.1 hu).1
  have hvZ : v ∈ quasithinOmegaOneCenter T := (mem_inf.1 hv).1
  have hu₂ : u ∉ centralizer (H₂ : Set G) := fun h' => hu1 (by
    have : u ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨hu, mem_inf.2 ⟨huZ, h'⟩⟩
    rwa [hZinf, mem_bot] at this)
  have hv₁ : v ∉ centralizer (H₁ : Set G) := fun h' => hv1 (by
    have : v ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨mem_inf.2 ⟨hvZ, h'⟩, hv⟩
    rwa [hZinf, mem_bot] at this)
  rcases hP₂ with h2X | h2X
  · have h1X : (H₁.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2 :=
      hP₁.resolve_left fun h1X => hne (h1X.trans h2X.symm)
    refine ⟨⟨K₀, h, hH₀, hH₀M, hsup, hK₀', hmax, hK, hN, ψ, hψ, hker, hTψ, hKψ, hcent, σ, hσ,
      H₂, H₁, le_sup_right, le_sup_left, h2X, h1X, ⟨v, s1347_Z_le_V0 hvZ⟩,
      ⟨u, s1347_Z_le_V0 huZ⟩, (mem_inf.1 hv).2, (mem_inf.1 hu).2, hv₁, hu₂, fun z hz => ?_,
      hvZ, huZ⟩⟩
    rcases hZ z hz with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (h'.trans (s1347_Z_comm huZ hvZ))))
  · have h1X : (H₁.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1 :=
      hP₁.resolve_right fun h1X => hne (h1X.trans h2X.symm)
    exact ⟨⟨K₀, h, hH₀, hH₀M, hsup, hK₀', hmax, hK, hN, ψ, hψ, hker, hTψ, hKψ, hcent, σ, hσ,
      H₁, H₂, le_sup_left, le_sup_right, h1X, h2X, ⟨u, s1347_Z_le_V0 huZ⟩,
      ⟨v, s1347_Z_le_V0 hvZ⟩, (mem_inf.1 hu).2, (mem_inf.1 hv).2, hu₂, hv₁, hZ, huZ, hvZ⟩⟩

namespace Data2

variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

theorem KH (D : Data2 S H₁ H₂) : D.K₀ ≤ H₁ ⊔ H₂ := le_of_mem_cComp D.hK₀

theorem reduced (D : Data2 S H₁ H₂) : IsTwoReducedIn (H₁ ⊔ H₂) (v0Of T H₁ H₂) :=
  s1347_reduced S D.hH₀

theorem sylow (D : Data2 S H₁ H₂) : IsSylowTwoOf T (H₁ ⊔ H₂) :=
  A5.isSylowTwoOf_of_le S.h13.sylow D.hH₀.1

theorem isMulCommutative (D : Data2 S H₁ H₂) : IsMulCommutative ↥(v0Of T H₁ H₂) :=
  D.reduced.2.2.1.1

theorem sq_eq_one (D : Data2 S H₁ H₂) {w : G} (hw : w ∈ v0Of T H₁ H₂) : w ^ 2 = 1 :=
  D.reduced.2.2.1.2 w hw

theorem exists_mem_K (D : Data2 S H₁ H₂) (g : SL3.S) :
    ∃ k : ↥(H₁ ⊔ H₂), (k : G) ∈ D.K₀ ∧ D.ψ k = g := by
  obtain ⟨k, hk, rfl⟩ : g ∈ (D.K₀.subgroupOf (H₁ ⊔ H₂)).map D.ψ := D.hKψ ▸ mem_top g
  exact ⟨k, mem_subgroupOf.1 hk, rfl⟩

theorem sigma_fix (D : Data2 S H₁ H₂) {h : ↥(H₁ ⊔ H₂)} {w : ↥(v0Of T H₁ H₂)}
    (hw : (h : G) * w = w * h) : D.σ (D.ψ h) w = w := by
  apply Subtype.ext
  rw [D.hσ, hw, mul_inv_cancel_right]

theorem sigma_fix_iff (D : Data2 S H₁ H₂) (h : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)) :
    D.σ (D.ψ h) w = w ↔ (h : G) * w = w * h := by
  constructor
  · intro hw
    have := congrArg Subtype.val hw
    rw [D.hσ, mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro hw
    exact D.sigma_fix hw

theorem sigma_fix_Z (D : Data2 S H₁ H₂) {g : SL3.S} (hg : g ∈ SL3.P0) {w : ↥(v0Of T H₁ H₂)}
    (hw : (w : G) ∈ quasithinOmegaOneCenter T) : D.σ g w = w := by
  obtain ⟨t, ht, rfl⟩ : g ∈ (T.subgroupOf (H₁ ⊔ H₂)).map D.ψ := D.hTψ ▸ hg
  exact D.sigma_fix (mem_centralizer_iff.1 (s134_Z_le_center T hw).2 _ (mem_subgroupOf.1 ht))

theorem sigma_fix_x (D : Data2 S H₁ H₂) {g : SL3.S} (hg : g ∈ SL3.X1) : D.σ g D.x = D.x := by
  obtain ⟨h, hh, rfl⟩ : g ∈ (D.Hp.subgroupOf (H₁ ⊔ H₂)).map D.ψ := D.hpX ▸ hg
  exact D.sigma_fix (mem_centralizer_iff.1 D.hxp _ (mem_subgroupOf.1 hh))

theorem sigma_fix_y (D : Data2 S H₁ H₂) {g : SL3.S} (hg : g ∈ SL3.X2) : D.σ g D.y = D.y := by
  obtain ⟨h, hh, rfl⟩ : g ∈ (D.Hl.subgroupOf (H₁ ⊔ H₂)).map D.ψ := D.hlX ▸ hg
  exact D.sigma_fix (mem_centralizer_iff.1 D.hyl _ (mem_subgroupOf.1 hh))

theorem exists_move_x (D : Data2 S H₁ H₂) : ∃ g ∈ SL3.X2, D.σ g D.x ≠ D.x := by
  have h := D.hxnl
  rw [mem_centralizer_iff] at h
  push Not at h
  obtain ⟨k, hk, hkx⟩ := h
  refine ⟨D.ψ ⟨k, D.hHl hk⟩, D.hlX ▸ mem_map_of_mem _ (mem_subgroupOf.2 hk), fun h1 => hkx ?_⟩
  exact ((D.sigma_fix_iff _ _).1 h1)

theorem exists_move_y (D : Data2 S H₁ H₂) : ∃ g ∈ SL3.X1, D.σ g D.y ≠ D.y := by
  have h := D.hynp
  rw [mem_centralizer_iff] at h
  push Not at h
  obtain ⟨k, hk, hky⟩ := h
  refine ⟨D.ψ ⟨k, D.hHp hk⟩, D.hpX ▸ mem_map_of_mem _ (mem_subgroupOf.2 hk), fun h1 => hky ?_⟩
  exact ((D.sigma_fix_iff _ _).1 h1)

theorem eq_one_of_fixed (D : Data2 S H₁ H₂) (w : ↥(v0Of T H₁ H₂)) (hw : ∀ g, D.σ g w = w) :
    w = 1 := by
  have hwT : (w : G) ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    have h1 := hw (D.ψ ⟨t, D.hH₀.1 ht⟩)
    exact (D.sigma_fix_iff _ _).1 h1
  have hwZ := s1347_centralizer_T_le S D.hH₀ w.2 hwT
  obtain ⟨gx, hgx, hgx'⟩ := D.exists_move_x
  obtain ⟨gy, hgy, hgy'⟩ := D.exists_move_y
  rcases D.hZ _ hwZ with h | h | h | h
  · exact Subtype.ext h
  · exact absurd (hw gx) (by rw [show w = D.x from Subtype.ext h]; exact hgx')
  · exact absurd (hw gy) (by rw [show w = D.y from Subtype.ext h]; exact hgy')
  · exfalso
    have hw' : w = D.x * D.y := Subtype.ext h
    apply hgy'
    have h1 := hw gy
    rw [hw', map_mul, D.sigma_fix_x hgy] at h1
    exact mul_left_cancel h1

theorem Z_le_commutator (D : Data2 S H₁ H₂) :
    quasithinOmegaOneCenter T ≤ ⁅D.K₀, v0Of T H₁ H₂⁆ := by
  have := D.isMulCommutative
  intro z hz
  have hzV : z ∈ v0Of T H₁ H₂ := s1347_Z_le_V0 hz
  have hmem := mem_closure_of_fixed_odd (K := SL3.S) (M := ↥(v0Of T H₁ H₂))
    (fun m => Subtype.ext (D.sq_eq_one m.2)) D.σ D.eq_one_of_fixed SL3.P0_sylow.2
    (v := ⟨z, hzV⟩) (fun s hs => D.sigma_fix_Z hs hz)
  have hle : Subgroup.closure {w : ↥(v0Of T H₁ H₂) | ∃ g m, D.σ g m * m⁻¹ = w} ≤
      (⁅D.K₀, v0Of T H₁ H₂⁆).subgroupOf (v0Of T H₁ H₂) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, m, rfl⟩
    obtain ⟨k, hk, rfl⟩ := D.exists_mem_K g
    rw [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, D.hσ, Subgroup.coe_inv]
    exact commutator_mem_commutator hk m.2
  exact mem_subgroupOf.1 (hle hmem)

theorem mem_P0_of_fix_xy (D : Data2 S H₁ H₂) {g : SL3.S}
    (hg : D.σ g (D.x * D.y) = D.x * D.y) : g ∈ SL3.P0 := by
  let St : Subgroup SL3.S :=
    (MulAction.stabilizer (MulAut ↥(v0Of T H₁ H₂)) (D.x * D.y)).comap D.σ
  have hmemSt : ∀ g, g ∈ St ↔ D.σ g (D.x * D.y) = D.x * D.y := fun g => Iff.rfl
  have hP0 : SL3.P0 ≤ St := fun g hg => (hmemSt g).2 (by
    rw [map_mul, D.sigma_fix_Z hg D.hxZ, D.sigma_fix_Z hg D.hyZ])
  obtain ⟨gx, hgx, hgx'⟩ := D.exists_move_x
  obtain ⟨gy, hgy, hgy'⟩ := D.exists_move_y
  have hX1 : ¬ SL3.X1 ≤ St := fun h => hgy' (by
    have h1 := (hmemSt gy).1 (h hgy)
    rw [map_mul, D.sigma_fix_x hgy] at h1
    exact mul_left_cancel h1)
  have hX2 : ¬ SL3.X2 ≤ St := fun h => hgx' (by
    have h1 := (hmemSt gx).1 (h hgx)
    rw [map_mul, D.sigma_fix_y hgx] at h1
    exact mul_right_cancel h1)
  rcases SL3.overgroups_SL3 St hP0 with h | h | h | h
  · exact h ▸ (hmemSt g).2 hg
  · exact absurd h.ge hX1
  · exact absurd h.ge hX2
  · exact absurd (h ▸ le_top) hX1

theorem isTwo_of_comm_xy (D : Data2 S H₁ H₂) {k : G} (hk : k ∈ D.K₀)
    (hc : k * ((D.x : G) * D.y) = ((D.x : G) * D.y) * k) : ∃ n : ℕ, k ^ 2 ^ n = 1 := by
  have hkH := D.KH hk
  have hg : D.ψ ⟨k, hkH⟩ ∈ SL3.P0 := D.mem_P0_of_fix_xy (D.sigma_fix (w := D.x * D.y) hc)
  have h8 : D.ψ ⟨k, hkH⟩ ^ 8 = 1 := by
    have := pow_card_eq_one' (G := ↥SL3.P0) (x := ⟨_, hg⟩)
    rw [SL3.card_P0] at this
    exact congrArg Subtype.val this
  have hk8 : ((⟨k, hkH⟩ ^ 8 : ↥(H₁ ⊔ H₂)) : G) ∈ pCoreOf 2 (H₁ ⊔ H₂) :=
    (map_eq_one_iff_of_ker D.hker _).1 (by rw [map_pow, h8])
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (H₁ ⊔ H₂)) ⟨_, hk8⟩
  refine ⟨m + 3, ?_⟩
  have h1 := congrArg Subtype.val hm
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
  rw [show 2 ^ (m + 3) = 8 * 2 ^ m by ring, pow_mul]
  exact h1

@[expose] def g3X1 : SL3.S := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide +kernel⟩

@[expose] def g3X2 : SL3.S := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide +kernel⟩

theorem g3X1_mem : g3X1 ∈ SL3.X1 := by
  show SL3.InX1 g3X1
  decide +kernel

theorem g3X2_mem : g3X2 ∈ SL3.X2 := by
  show SL3.InX2 g3X2
  decide +kernel

theorem g3X1_pow : g3X1 ^ 3 = 1 ∧ g3X1 ≠ 1 := by decide +kernel

theorem g3X2_pow : g3X2 ^ 3 = 1 ∧ g3X2 ≠ 1 := by decide +kernel

theorem pow_two_pow_ne_one {Γ : Type*} [Group Γ] {γ : Γ} (h3 : γ ^ 3 = 1) (h1 : γ ≠ 1)
    (n : ℕ) : γ ^ 2 ^ n ≠ 1 := by
  intro h2
  apply h1
  have hd : orderOf γ ∣ Nat.gcd 3 (2 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.1 hd

theorem pow_ne_one_of_lift (D : Data2 S H₁ H₂) {γ : SL3.S} (h3 : γ ^ 3 = 1) (h1 : γ ≠ 1)
    {k : ↥(H₁ ⊔ H₂)} (hk : D.ψ k = γ) (n : ℕ) : (k : G) ^ 2 ^ n ≠ 1 := by
  intro hn
  apply pow_two_pow_ne_one h3 h1 n
  rw [← hk, ← map_pow]
  have : k ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
  rw [this, map_one]

theorem exists_comm_x (D : Data2 S H₁ H₂) :
    ∃ k ∈ D.K₀, k * (D.x : G) = D.x * k ∧ ∀ n : ℕ, k ^ 2 ^ n ≠ 1 := by
  obtain ⟨k, hk, hkγ⟩ := D.exists_mem_K g3X1
  refine ⟨k, hk, (D.sigma_fix_iff k D.x).1 (hkγ ▸ D.sigma_fix_x g3X1_mem), ?_⟩
  exact D.pow_ne_one_of_lift g3X1_pow.1 g3X1_pow.2 hkγ

theorem exists_comm_y (D : Data2 S H₁ H₂) :
    ∃ k ∈ D.K₀, k * (D.y : G) = D.y * k ∧ ∀ n : ℕ, k ^ 2 ^ n ≠ 1 := by
  obtain ⟨k, hk, hkγ⟩ := D.exists_mem_K g3X2
  refine ⟨k, hk, (D.sigma_fix_iff k D.y).1 (hkγ ▸ D.sigma_fix_y g3X2_mem), ?_⟩
  exact D.pow_ne_one_of_lift g3X2_pow.1 g3X2_pow.2 hkγ

theorem mem_Z_of_fixed (D : Data2 S H₁ H₂) {w : G} (hw : w ∈ v0Of T H₁ H₂)
    (hfix : ∀ s ∈ T ⊓ D.K₀, s * w = w * s) : w ∈ quasithinOmegaOneCenter T := by
  refine s1347_centralizer_T_le S D.hH₀ hw (mem_centralizer_iff.2 fun t ht => ?_)
  obtain ⟨k, hk, hkt⟩ := D.exists_mem_K (D.ψ ⟨t, D.hH₀.1 ht⟩)
  have hkt' : ((k * (⟨t, D.hH₀.1 ht⟩ : ↥(H₁ ⊔ H₂))⁻¹ : ↥(H₁ ⊔ H₂)) : G) ∈
      pCoreOf 2 (H₁ ⊔ H₂) :=
    (map_eq_one_iff_of_ker D.hker _).1 (by rw [map_mul, map_inv, hkt, mul_inv_cancel])
  have hkT : (k : G) ∈ T := by
    have h1 := pCoreOf_two_le_of_isSylowTwoOf D.sylow hkt'
    have h2 : (k : G) = ((k * (⟨t, D.hH₀.1 ht⟩ : ↥(H₁ ⊔ H₂))⁻¹ : ↥(H₁ ⊔ H₂)) : G) * t := by
      simp
    rw [h2]
    exact T.mul_mem h1 ht
  have h1 := D.sigma_fix (w := ⟨w, hw⟩) (hfix k ⟨hkT, hk⟩)
  rw [hkt] at h1
  exact (D.sigma_fix_iff _ _).1 h1

theorem center_SL3 : Subgroup.center SL3.S = ⊥ := by
  have := HSType.isSimpleGroup_SL_three_two
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center SL3.S) with h | h
  · exact h
  · exfalso
    have h1 : SL3.ex ∈ Subgroup.center SL3.S := h ▸ mem_top _
    have h2 := Subgroup.mem_center_iff.1 h1 SL3.w3
    revert h2
    decide +kernel

theorem mem_pCoreOf_of_comm (D : Data2 S H₁ H₂) {a : G} (ha : a ∈ H₁ ⊔ H₂)
    (hc : ∀ k ∈ D.K₀, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 (H₁ ⊔ H₂)) :
    a ∈ pCoreOf 2 (H₁ ⊔ H₂) := by
  have hψa : D.ψ ⟨a, ha⟩ ∈ Subgroup.center SL3.S := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, hk, rfl⟩ := D.exists_mem_K g
    have h0 : ((⟨a, ha⟩ * k * (⟨a, ha⟩ : ↥(H₁ ⊔ H₂))⁻¹ * k⁻¹ : ↥(H₁ ⊔ H₂)) : G) ∈
        pCoreOf 2 (H₁ ⊔ H₂) := by
      simpa using hc k hk
    have h1 := (map_eq_one_iff_of_ker D.hker _).2 h0
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [center_SL3, mem_bot] at hψa
  exact (map_eq_one_iff_of_ker D.hker _).1 hψa

theorem noFF (D : Data2 S H₁ H₂) {A : Subgroup G} (hAT : A ≤ T) (hAe : IsElemAbelian 2 A)
    (hAC : ¬ A ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)).relIndex A *
      Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer (A : Set G)) < Nat.card ↥(v0Of T H₁ H₂) := by
  have hcomm : IsMulCommutative ↥(v0Of T H₁ H₂) := D.isMulCommutative
  have h2 : ∀ m : Additive ↥(v0Of T H₁ H₂), m + m = 0 := by
    intro m
    have : Additive.toMul m * Additive.toMul m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact D.sq_eq_one (Additive.toMul m).2)
    exact congrArg Additive.ofMul this
  obtain ⟨hx, hy, hxl', hyp'⟩ :=
    s1347_l32_hyps D.hσ D.hpX D.hlX D.hHl D.hHp D.hxp D.hyl D.hxnl D.hynp
  have hgen := s1347_l32_gen D.hσ D.hZ
  have hC := s1347_l32_fixed S D.hH₀ D.hTψ D.hσ D.hZ
  have key : ∀ {A' : Subgroup SL3.S}, A' ≤ H6.borel → A' ≠ ⊥ → (∀ a ∈ A', a * a = 1) →
      Nat.card A' * Nat.card (L32Mod.Fix (L32Mod.toAddRep D.σ) A') <
        Nat.card (Additive ↥(v0Of T H₁ H₂)) := by
    intro A' hAT' hA hA2
    rcases L32Mod.l32_cases h2 hx hy hxl' hyp' hgen hC with hiso | hiso |
      ⟨U₁, U₂, hsup, hinf, hinv₁, hinv₂, ⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
    · exact L32Mod.noOffender_core hiso hAT' hA hA2
    · exact L32Mod.noOffender_core_graph hiso hAT' hA hA2
    · exact L32Mod.noOffender_sum (L32Mod.isoMod_sum hsup hinf e₁ he₁ hinv₁ hinv₂ e₂ he₂)
        hAT' hA hA2
  have hAH : A ≤ H₁ ⊔ H₂ := hAT.trans D.hH₀.1
  have hA'T : (A.subgroupOf (H₁ ⊔ H₂)).map D.ψ ≤ H6.borel := fun g hg =>
    (borel_iff_P0 g).2 (D.hTψ ▸ map_mono (fun a ha => mem_subgroupOf.2
      (hAT (mem_subgroupOf.1 ha))) hg)
  have hA'1 : (A.subgroupOf (H₁ ⊔ H₂)).map D.ψ ≠ ⊥ := by
    intro hb
    apply hAC
    intro a ha
    have h1 : D.ψ ⟨a, hAH ha⟩ = 1 := by
      have : D.ψ ⟨a, hAH ha⟩ ∈ (A.subgroupOf (H₁ ⊔ H₂)).map D.ψ :=
        mem_map_of_mem _ (mem_subgroupOf.2 ha)
      rw [hb, mem_bot] at this
      exact this
    have := (map_eq_one_iff_of_ker D.hker _).1 h1
    rw [← D.hcent] at this
    exact this.2
  have hA'2 : ∀ a ∈ (A.subgroupOf (H₁ ⊔ H₂)).map D.ψ, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : (a : G) * a = 1 := by
      rw [← pow_two]
      exact hAe.2 _ (mem_subgroupOf.1 ha)
    rw [show a * a = 1 from Subtype.ext this, map_one]
  have hcardA : Nat.card ↥((A.subgroupOf (H₁ ⊔ H₂)).map D.ψ) =
      (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)).relIndex A := by
    rw [← relIndex_ker, D.hker, ← pCoreOf_subgroupOf_eq_pCore,
      relIndex_subgroupOf hAH, ← D.hcent, inf_comm A, ← inf_relIndex_right]
    congr 1
    rw [inf_comm (H₁ ⊔ H₂), inf_assoc, inf_eq_right.2 hAH]
  have hcardF : Nat.card (L32Mod.Fix (L32Mod.toAddRep D.σ) ((A.subgroupOf (H₁ ⊔ H₂)).map D.ψ)) =
      Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer (A : Set G)) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨((Additive.toMul m.1 : ↥(v0Of T H₁ H₂)) : G),
          mem_inf.2 ⟨(Additive.toMul m.1).2,
          mem_centralizer_iff.2 fun a ha => ?_⟩⟩
        invFun := fun w => ⟨Additive.ofMul ⟨w, (mem_inf.1 w.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := m.2 (D.ψ ⟨a, hAH ha⟩) (mem_map_of_mem _ (mem_subgroupOf.2 ha))
      exact ((s1347_fix_iff D.hσ _ _).1 this)
    · rintro _ ⟨a, ha, rfl⟩
      exact (s1347_fix_iff D.hσ _ _).2 (mem_centralizer_iff.1 (mem_inf.1 w.2).2 a
        (mem_subgroupOf.1 ha))
  have := key hA'T hA'1 hA'2
  rw [hcardA, hcardF] at this
  exact this

end Data2

end CFSG.Quasithin.H13.U3.P2
