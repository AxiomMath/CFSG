module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Arc.two {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : a ≠ c) : Arc Γ 2 where
  vert i := if i = 0 then a else if i = 1 then b else c
  adj i hi := by
    interval_cases i
    · simpa using hab
    · simpa using hbc
  nb i hi := by
    obtain rfl : i = 0 := by omega
    simpa using hac

theorem Arc.two_vert_zero {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : a ≠ c) :
    (Arc.two hab hbc hac).vert 0 = a := by simp [Arc.two]

theorem Arc.two_vert_one {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : a ≠ c) :
    (Arc.two hab hbc hac).vert 1 = b := by simp [Arc.two]

theorem Arc.two_vert_two {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : a ≠ c) :
    (Arc.two hab hbc hac).vert 2 = c := by simp [Arc.two]

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem eq_of_adj_adj {u₁ u₂ x y : V} (h1x : Γ.Adj u₁ x) (hx2 : Γ.Adj x u₂) (h1y : Γ.Adj u₁ y)
    (hy2 : Γ.Adj y u₂) (hne : u₁ ≠ u₂) : x = y := by
  have := Arc.vert_eq_of_ends F.isTree (Arc.two h1x hx2 hne) (Arc.two h1y hy2 hne) rfl rfl 1
    (by norm_num)
  simpa [Arc.two] using this

theorem exists_adj_ne (v w : V) : ∃ u, Γ.Adj v u ∧ u ≠ w := by
  by_contra h
  push Not at h
  have h3 : 3 ≤ Nat.card (Γ.neighborSet v) := by rcases F.valence v with h | h <;> omega
  have hsub : Γ.neighborSet v ⊆ {w} := fun u hu => h u hu
  have hc : (Γ.neighborSet v).ncard ≤ 1 := by
    calc (Γ.neighborSet v).ncard ≤ ({w} : Set V).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton w)
      _ = 1 := Set.ncard_singleton w
  rw [← Nat.card_coe_set_eq] at hc
  omega

theorem nbrStab_le_stabilizer (v : V) : nbrStab Γ G v ≤ MulAction.stabilizer G v := by
  intro g hg
  obtain ⟨u₁, hu₁⟩ := F.exists_adj v
  obtain ⟨u₂, hu₂, hne⟩ := F.exists_adj_ne v u₁
  have e₁ : g • u₁ = u₁ := hg u₁ hu₁
  have e₂ : g • u₂ = u₂ := hg u₂ hu₂
  have h1 : Γ.Adj u₁ (g • v) := by
    have := (F.adj_smul g v u₁).2 hu₁
    rw [e₁] at this
    exact this.symm
  have h2 : Γ.Adj (g • v) u₂ := by
    have := (F.adj_smul g v u₂).2 hu₂
    rw [e₂] at this
    exact this
  exact (F.eq_of_adj_adj hu₁.symm hu₂ h1 h2 hne.symm).symm

theorem nbrStab_le_edge (v : V) {w : V} (hw : Γ.Adj v w) :
    nbrStab Γ G v ≤ MulAction.stabilizer G v ⊓ MulAction.stabilizer G w := fun _ hg =>
  ⟨F.nbrStab_le_stabilizer v hg, MulAction.mem_stabilizer_iff.2 (hg w hw)⟩

theorem nbrStab_isPGroup (v : V) : IsPGroup 2 (nbrStab Γ G v) := by
  obtain ⟨w, hw⟩ := F.exists_adj v
  exact (F.edge_two v w hw).to_le (F.nbrStab_le_edge v hw)

theorem finite_stabilizer_inf (u v : V) :
    Finite ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v) :=
  haveI := F.loc_finite u
  Finite.of_injective (Subgroup.inclusion (inf_le_left : _ ≤ MulAction.stabilizer G u))
    (Subgroup.inclusion_injective _)

theorem not_nbrStab_le_nbrStab (h40 : Fan40 F) {b c : V} (hbc : Γ.Adj b c) :
    ¬ nbrStab Γ G b ≤ nbrStab Γ G c := by
  intro hle
  obtain ⟨a, hab, hac⟩ := F.exists_adj_ne b c
  obtain ⟨w, hcw, hwb⟩ := F.exists_adj_ne c b
  refine h40 2 (by norm_num) (by norm_num) ⟨Arc.two hab.symm hbc hac, w, ?_, ?_, ?_⟩
  · rw [Arc.two_vert_two]
    exact hcw
  · rw [show (2 : ℕ) - 1 = 1 from rfl, Arc.two_vert_one]
    exact hwb
  · intro g hg
    rw [mem_stabRange] at hg
    have hga : g • a = a := by simpa [Arc.two] using hg 0 (Nat.zero_le _) (by norm_num)
    have hgb : g • b = b := by simpa [Arc.two] using hg 1 (by norm_num) (by norm_num)
    have hgc : g • c = c := by simpa [Arc.two] using hg 2 (by norm_num) le_rfl
    have hK : g ∈ nbrStab Γ G b := fun z hz =>
      F.frobenius_two b a c hab hbc hac g (MulAction.mem_stabilizer_iff.2 hgb) hga hgc z hz
    exact hle hK w hcw

theorem nbrStab_ne_bot (h40 : Fan40 F) (b : V) : nbrStab Γ G b ≠ ⊥ := by
  intro h
  obtain ⟨c, hc⟩ := F.exists_adj b
  exact F.not_nbrStab_le_nbrStab h40 hc (h ▸ bot_le)

end FanTree

theorem exists_involution_of_le_edge (F : FanTree Γ G) {u v : V} (huv : Γ.Adj u v)
    {H : Subgroup G} (hH : H ≤ MulAction.stabilizer G u ⊓ MulAction.stabilizer G v)
    (hne : H ≠ ⊥) : ∃ x ∈ H, x ≠ 1 ∧ x * x = 1 := by
  have hpg : IsPGroup 2 H := (F.edge_two u v huv).to_le hH
  have := F.finite_stabilizer_inf u v
  have hfin : Finite H :=
    Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective _)
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne ((Subgroup.card_eq_one).1 (by simpa using hn))
  have hdvd : 2 ∣ Nat.card H := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 hdvd
  refine ⟨x, x.2, ?_, ?_⟩
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  · have := pow_orderOf_eq_one x
    rw [hx, sq] at this
    exact congrArg Subtype.val this

theorem omega1_le_omega1_of_inv {H K : Subgroup G} (h : ∀ x ∈ H, x * x = 1 → x ∈ K) :
    omega1 H ≤ omega1 K :=
  (Subgroup.closure_le _).2 fun _ hx => Subgroup.subset_closure ⟨h _ hx.1 hx.2, hx.2⟩

theorem omega1_eq_of_le_of_omega1_le {H K : Subgroup G} (hHK : H ≤ K) (h : omega1 K ≤ H) :
    omega1 H = omega1 K :=
  le_antisymm (omega1_mono hHK)
    (omega1_le_omega1_of_inv fun _ hx hx2 => h (Subgroup.subset_closure ⟨hx, hx2⟩))

theorem mem_normalizer_omega1 {K : Subgroup G} {g : G} (h1 : ∀ h ∈ K, g * h * g⁻¹ ∈ K)
    (h2 : ∀ h ∈ K, g⁻¹ * h * g ∈ K) : g ∈ Subgroup.normalizer (omega1 K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => omega1_conj_mem h1 hy
  · intro hy
    have := omega1_conj_mem (g := g⁻¹) (H := K) (H' := K) (fun h hh => by simpa using h2 h hh)
      hy
    simpa [mul_assoc] using this

end CFSG.Quasithin.Fan86
