module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveSwap
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveFin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Twelve

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}
variable {α' ν β l : Geo H M}

theorem Data.Qv_le_edge (hA : F53Amalgam H M S) (d : Data α α' ν β l) :
    Qv α' ≤ stab l ⊓ stab α' :=
  le_inf (Qv_le_stab_of_mem_nbrs hA d.hl) (pCoreOf_le 2 _)

theorem Data.ψ_mem_That (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l))
    {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {a : G}
    (ha : a ∈ Wn α ⊓ Qv α') : D'.ψ ⟨a, Qv_le_stab_of_mem_nbrs hA d.hl ha.2⟩ ∈ S5ThatF := by
  have ht := (mem_S5Syl_iff _).mp (D'.ψ_mem_S5Syl (d.Qv_le_edge hA hz₁.2))
  have hσ := (mem_S5Syl_iff _).mp (D'.ψ_mem_S5Syl (d.Qv_le_edge hA ha.2))
  obtain ⟨h1, h2, h3⟩ := (isSwap_iff _).mp hsw'
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  have hcomm : a * z₁ = z₁ * a := comm_of_elemAbelian hW ha.1 (hs.Zv_le_Wn hA h26 hz₁.1)
  refine mem_S5ThatF_of_commute _ ht h1 h2 h3 _ hσ ?_
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

theorem Data.commute_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {a : G}
    (ha : a ∈ Wn α ⊓ Qv α') {y : G} (hy : y ∈ Yv α') : a * y = y * a := by
  have hT := (mem_S5That_iff _).mpr (d.ψ_mem_That hA h26 hs hb5 D' hz₁ hsw' ha)
  have hc := (D'.mem_centralizer_Y_iff ⟨a, Qv_le_stab_of_mem_nbrs hA d.hl ha.2⟩).mpr hT
  rw [← hs.Yv_eq_comm_comm hA h26 (d.vtypes hA hs ho).1 d.hl] at hc
  exact (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm

theorem Data.comm_eq_or (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l))
    {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {u : G} (hu : u ∈ Zv l)
    (hcu : z₁ * u = u * z₁) {a a' : G} (ha : a ∈ Wn α ⊓ Qv α') (ha' : a' ∈ Wn α ⊓ Qv α') :
    ⁅a, u⁆ = 1 ∨ ⁅a', u⁆ = 1 ∨ ⁅a, u⁆ = ⁅a', u⁆ := by
  obtain ⟨w, rfl⟩ : u ∈ D'.φ.range := D'.range_eq.ge hu
  have ht := (mem_S5Syl_iff _).mp (D'.ψ_mem_S5Syl (d.Qv_le_edge hA hz₁.2))
  obtain ⟨h1, h2, h3⟩ := (isSwap_iff _).mp hsw'
  have hfix : orth.act (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩) w = w := by
    apply D'.inj
    rw [D'.act_eq, hcu]
    group
  have key := act_comm_eq _ ht h1 h2 h3 w hfix _ (d.ψ_mem_That hA h26 hs hb5 D' hz₁ hsw' ha) _
    (d.ψ_mem_That hA h26 hs hb5 D' hz₁ hsw' ha')
  rw [comm_φ_eq D' (Qv_le_stab_of_mem_nbrs hA d.hl ha.2),
    comm_φ_eq D' (Qv_le_stab_of_mem_nbrs hA d.hl ha'.2)]
  rcases key with h | h | h
  · left; rw [h, map_one]
  · right; left; rw [h, map_one]
  · right; right; rw [h]

theorem Data.comm_eq_one_of_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l))
    {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {u : G} (hu : u ∈ Zv l)
    (hcu : z₁ * u = u * z₁) {a : G} (ha : a ∈ Wn α ⊓ Qv α') {v₀ : G} (hv₀ : v₀ ∈ Zv l)
    (h : ⁅a, u⁆ = ⁅v₀, z₁⁆) : ⁅a, u⁆ = 1 := by
  obtain ⟨w, rfl⟩ : u ∈ D'.φ.range := D'.range_eq.ge hu
  obtain ⟨w₀, rfl⟩ : v₀ ∈ D'.φ.range := D'.range_eq.ge hv₀
  have ht := (mem_S5Syl_iff _).mp (D'.ψ_mem_S5Syl (d.Qv_le_edge hA hz₁.2))
  obtain ⟨h1, h2, h3⟩ := (isSwap_iff _).mp hsw'
  have hfix : orth.act (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩) w = w := by
    apply D'.inj
    rw [D'.act_eq, hcu]
    group
  rw [comm_φ_eq D' (Qv_le_stab_of_mem_nbrs hA d.hl ha.2),
    comm_φ_eq' D' (Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2)] at h
  rw [comm_φ_eq D' (Qv_le_stab_of_mem_nbrs hA d.hl ha.2),
    act_comm_eq_one _ ht h1 h2 h3 w hfix _ (d.ψ_mem_That hA h26 hs hb5 D' hz₁ hsw' ha) w₀
      (D'.inj h), map_one]

theorem Data.comm_eq_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {u : G}
    (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α) {a : G} (ha : a ∈ Wn α ⊓ Qv α') {v : G}
    (hv : v ∈ Zv l ⊓ Qv β) : ⁅a, v⁆ = 1 ∨ ⁅a, v⁆ = ⁅a, u⁆ := by
  by_cases hvQ : v ∈ Qv α
  · left
    have hvY := d.Zv_inf_Qv_le_Yv hA h26 hs ho ⟨hv.1, hvQ⟩
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact d.commute_Yv hA h26 hs ho hb5 D' hz₁ hsw' ha hvY
  · right
    have hy := d.inv_mul_mem_Yv hA h26 hs ho (by omega) hu huQ hv hvQ
    have hc := d.commute_Yv hA h26 hs ho hb5 D' hz₁ hsw' ha hy
    have hy' : a * (u⁻¹ * v) * a⁻¹ = u⁻¹ * v := by rw [hc]; group
    calc ⁅a, v⁆ = (a * u * a⁻¹) * (a * (u⁻¹ * v) * a⁻¹) * (u⁻¹ * v)⁻¹ * u⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (a * u * a⁻¹) * (u⁻¹ * v) * (u⁻¹ * v)⁻¹ * u⁻¹ := by rw [hy']
      _ = ⁅a, u⁆ := by simp only [commutatorElement_def]; group

theorem Data.Hcomm_eq_bot_of_forall (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {u : G}
    (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α) (hall : ∀ a ∈ Wn α ⊓ Qv α', ⁅a, u⁆ = 1) :
    Hcomm α α' β l = ⊥ := by
  rw [eq_bot_iff]
  unfold Hcomm
  rw [Subgroup.commutator_le]
  intro a ha v hv
  rcases d.comm_eq_comm hA h26 hs ho hb5 D' hz₁ hsw' hu huQ ha hv with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h, hall a ha]; exact Subgroup.one_mem _

theorem Data.card_Hcomm_le_two_of_swap (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {u : G}
    (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α) (hcu : z₁ * u = u * z₁) :
    Nat.card (Hcomm α α' β l) ≤ 2 := by
  by_cases hall : ∀ a ∈ Wn α ⊓ Qv α', ⁅a, u⁆ = 1
  · rw [d.Hcomm_eq_bot_of_forall hA h26 hs ho hb5 D' hz₁ hsw' hu huQ hall, Subgroup.card_bot]
    norm_num
  · push Not at hall
    obtain ⟨a₀, ha₀, hne⟩ := hall
    have hd : ⁅a₀, u⁆ ∈ Zv l :=
      d.Hcomm_le_Zv hA (Subgroup.commutator_mem_commutator ha₀ hu)
    have hd2 : ⁅a₀, u⁆ ^ 2 = 1 := (isElemAbelian_Zv hA l).2 _ hd
    refine (Subgroup.card_le_of_le ?_).trans (card_zpowers_le_two hd2)
    unfold Hcomm
    rw [Subgroup.commutator_le]
    intro a ha v hv
    rcases d.comm_eq_comm hA h26 hs ho hb5 D' hz₁ hsw' hu huQ ha hv with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]
      rcases d.comm_eq_or hA h26 hs hb5 D' hz₁ hsw' hu.1 hcu ha ha₀ with h' | h' | h'
      · rw [h']; exact Subgroup.one_mem _
      · exact absurd h' hne
      · rw [h']; exact Subgroup.mem_zpowers _

theorem Data.Hcomm_eq_bot_of_swap (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M)
    (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ)) (d : Data α α' ν β l) {κ θ : Geo H M}
    (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M) (hθ : θ ∈ nbrs κ)
    (hdθ : dist α θ + 3 = bMin H M) (hB : ¬ Wn α ≤ stab α')
    (D' : Dict5 (stab l) (stab l ⊓ stab α') (Zv l)) {z₁ : G} (hz₁ : z₁ ∈ Zv α ⊓ Qv α')
    (hsw' : (D'.ψ ⟨z₁, Qv_le_stab_of_mem_nbrs hA d.hl hz₁.2⟩).IsSwap) {v₀ : G}
    (hv₀ : v₀ ∈ Zv l) (hne : ⁅v₀, z₁⁆ ≠ 1) {u : G} (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α)
    (hcu : z₁ * u = u * z₁) : Hcomm α α' β l = ⊥ := by
  refine d.Hcomm_eq_bot_of_forall hA h26 hs ho hb5 D' hz₁ hsw' hu huQ fun a ha => ?_
  by_contra hau
  have hI := d.card_Yv_inf_le_two hA h26 hs ho hκ (d.kappa_ne hdκ)
  have h1 : ⁅a, u⁆ ∈ Yv α' ⊓ Yv κ :=
    d.Hcomm_le_inf hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hB
      (Subgroup.commutator_mem_commutator ha hu)
  have h2 : ⁅v₀, z₁⁆ ∈ Yv α' ⊓ Yv κ :=
    d.comm_Zv_le_inf hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hB
      (Subgroup.commutator_mem_commutator hv₀ hz₁)
  exact hau (d.comm_eq_one_of_eq hA h26 hs hb5 D' hz₁ hsw' hu.1 hcu ha hv₀
    (eq_of_card_le_two hI h1 h2 hau hne))

theorem Data.secIdx_le_two_of_swap (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M)
    (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ)) (d : Data α α' ν β l) {κ θ : Geo H M}
    (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M) (hθ : θ ∈ nbrs κ)
    (hdθ : dist α θ + 3 = bMin H M) (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {u : G}
    (hu : u ∈ Zv l ⊓ Qv β) (huQ : u ∉ Qv α) (hsw : (D.ψ ⟨u, d.Qv_beta_le hA hu.2⟩).IsSwap) :
    secIdx (Subgroup.zpowers u) (Zv α) (Wn α) ≤ 2 := by
  obtain ⟨z₁, hz₁, v₀, hv₀, hne⟩ := d.exists_z₁ hA h26 hs ho (by omega)
  obtain ⟨D'⟩ := (hs.of_vtype_false (d.vtypes hA hs ho).2.1).exists_dict5 hA (nbrs_symm d.hl)
  have hsw' := d.ψ_isSwap hA h26 hs ho (by omega) D hu huQ hsw D' hz₁ hv₀ hne
  have hcu : z₁ * u = u * z₁ := d.commute_of_swap hA h26 hs ho (by omega) D hu huQ hsw hz₁
  have key := d.secIdx_le hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hu
  by_cases hB : Wn α ≤ stab α'
  · rw [inf_of_le_left hB, Subgroup.relIndex_self, one_mul] at key
    exact key.trans (d.card_Hcomm_le_two_of_swap hA h26 hs ho hb5 D' hz₁ hsw' hu huQ hcu)
  · rw [d.Hcomm_eq_bot_of_swap hA h26 hs ho hb5 hL hκ hdκ hθ hdθ hB D' hz₁ hsw' hv₀ hne hu huQ
      hcu, Subgroup.card_bot, mul_one] at key
    exact key.trans (relIndex_Wn_inf_stab_le_two hA h26 hs ho hb5 hL d.crit d.hν d.dν hκ hdκ hθ
      hdθ d.hβ d.dβ)

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
