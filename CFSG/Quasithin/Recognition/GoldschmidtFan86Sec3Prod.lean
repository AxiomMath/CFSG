module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Iface
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Ball
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Cop
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Frattini
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Local
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph
open scoped Pointwise

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure XSetup (_F : FanTree Γ G) (α β : V) (x : G) : Prop where
  adj : Γ.Adj α β
  mem : x ∈ MulAction.stabilizer G α
  ord : orderOf x = pval Γ α

structure ProdSetup (F : FanTree Γ G) (α β : V) (x : G) (H : Subgroup G) : Prop
    extends XSetup F α β x where
  coe : (H : Set G) = (Subgroup.zpowers x : Set G) * (nbrStab Γ G β : Set G)

theorem FanTree.odd_valence (F : FanTree Γ G) (v : V) : Odd (pval Γ v) := by
  have e : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
  rw [e]
  rcases F.valence v with h | h <;> rw [h]
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

namespace XSetup

variable {F : FanTree Γ G} {α β : V} {x : G} (S : XSetup F α β x)

include S

theorem pow_valence_eq_one : x ^ pval Γ α = 1 := by
  rw [← S.ord]
  exact pow_orderOf_eq_one x

theorem pow_smul_eq_self_iff (L : LocalFacts F) (i : ℕ) : x ^ i • β = β ↔ pval Γ α ∣ i := by
  have hp : (pval Γ α).Prime := F.valence_isPrime α
  constructor
  · intro h
    by_contra hdvd
    have hcop : Nat.Coprime (pval Γ α) i := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd
    have hi0 : i ≠ 0 := fun h0 => hdvd (h0 ▸ dvd_zero _)
    have hord' : orderOf (x ^ i) = pval Γ α := by
      rw [orderOf_pow' _ hi0, S.ord, hcop.gcd_eq_one, Nat.div_one]
    obtain ⟨γ, hγ, hγβ⟩ := F.exists_adj_ne α β
    obtain ⟨j, hj⟩ := L.pow_smul_eq (Subgroup.pow_mem _ S.mem i) hord' S.adj hγ
    have hfix : x ^ i ∈ MulAction.stabilizer G β := MulAction.mem_stabilizer_iff.2 h
    have := MulAction.mem_stabilizer_iff.1 (Subgroup.pow_mem _ hfix j)
    exact hγβ (hj.symm.trans this)
  · rintro ⟨j, rfl⟩
    rw [pow_mul, ← S.ord, pow_orderOf_eq_one, one_pow, one_smul]

theorem pow_eq_one_of_smul_eq (L : LocalFacts F) (i : ℕ) (h : x ^ i • β = β) : x ^ i = 1 := by
  have := (S.pow_smul_eq_self_iff L i).1 h
  rw [← S.ord] at this
  exact orderOf_dvd_iff_pow_eq_one.1 this

theorem eq_one_of_mem_zpowers (L : LocalFacts F) {c : G} (hc : c ∈ Subgroup.zpowers x)
    (hcK : c ∈ nbrStab Γ G β) : c = 1 := by
  have hfin : IsOfFinOrder x :=
    orderOf_pos_iff.1 (by rw [S.ord]; exact (F.valence_isPrime α).pos)
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hc)
  rw [← hi]
  exact S.pow_eq_one_of_smul_eq L i (by
    rw [hi]
    exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer β hcK))

theorem comm_mod_of_inf_eq (L : LocalFacts F)
    (h : nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α) :
    ∀ s ∈ nbrStab Γ G α, x * s * x⁻¹ * s⁻¹ ∈ ballStab Γ G 2 α := by
  have hKα : nbrStab Γ G α ≤ MulAction.stabilizer G α := F.nbrStab_le_stabilizer α
  have hle : nbrStab Γ G α ≤ MulAction.stabilizer G β ⊓ MulAction.stabilizer G α :=
    fun k hk => ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk β S.adj), hKα hk⟩
  obtain ⟨g, hgS, hg4, hgen⟩ := L.cyc S.adj.symm (nbrStab Γ G α) hle
  refine comm_mod_of_cyclic_four (ballStab Γ G 2 α) (nbrStab Γ G α)
    (fun k hk => F.mem_normalizer_ballStab_two (hKα hk)) (F.mem_normalizer_ballStab_two S.mem)
    (fun s hs => F.conj_mem_nbrStab_of_stab S.mem hs) (F.odd_valence α) S.pow_valence_eq_one hgS
    ?_ ?_
  · rw [← h]
    exact ⟨Subgroup.pow_mem _ hgS 4, hg4⟩
  · intro s hs
    obtain ⟨n, hn⟩ := hgen s hs
    refine ⟨n, ?_⟩
    rw [← h]
    exact ⟨(nbrStab Γ G α).mul_mem ((nbrStab Γ G α).zpow_mem hgS n)
      ((nbrStab Γ G α).inv_mem hs), hn⟩

end XSetup

namespace ProdSetup

variable {F : FanTree Γ G} {α β : V} {x : G} {H : Subgroup G} (S : ProdSetup F α β x H)

include S

theorem mem_prod_iff {h : G} : h ∈ H ↔ ∃ (i : ℕ) (k : G), k ∈ nbrStab Γ G β ∧ h = x ^ i * k := by
  have hfin : IsOfFinOrder x :=
    orderOf_pos_iff.1 (by rw [S.ord]; exact (F.valence_isPrime α).pos)
  rw [← SetLike.mem_coe, S.coe, Set.mem_mul]
  constructor
  · rintro ⟨c, hc, k, hk, rfl⟩
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hc)
    exact ⟨i, k, hk, by rw [hi]⟩
  · rintro ⟨i, k, hk, rfl⟩
    exact ⟨x ^ i, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i, k, hk, rfl⟩

theorem x_mem : x ∈ H := S.mem_prod_iff.2 ⟨1, 1, Subgroup.one_mem _, by simp⟩

theorem nbrStab_le : nbrStab Γ G β ≤ H := fun k hk => S.mem_prod_iff.2 ⟨0, k, hk, by simp⟩

theorem nbrStab_le_stab : nbrStab Γ G β ≤ MulAction.stabilizer G α :=
  fun _ hk => (F.nbrStab_le_edge β S.adj.symm hk).2

theorem le_stab : H ≤ MulAction.stabilizer G α := by
  intro h hh
  obtain ⟨i, k, hk, rfl⟩ := S.mem_prod_iff.1 hh
  exact mul_mem (Subgroup.pow_mem _ S.mem i) (S.nbrStab_le_stab hk)

theorem inf_stab (L : LocalFacts F) : H ⊓ MulAction.stabilizer G β = nbrStab Γ G β := by
  refine le_antisymm (fun h hh => ?_) fun k hk =>
    ⟨S.nbrStab_le hk, F.nbrStab_le_stabilizer β hk⟩
  obtain ⟨i, k, hk, rfl⟩ := S.mem_prod_iff.1 hh.1
  have h1 : (x ^ i * k) • β = β := MulAction.mem_stabilizer_iff.1 hh.2
  have h2 : k • β = β := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer β hk)
  rw [mul_smul, h2] at h1
  rw [S.toXSetup.pow_eq_one_of_smul_eq L i h1, one_mul]
  exact hk

theorem mem_nbrStab_of_mem (L : LocalFacts F) {g : G} (hg : g ∈ H) (hgα : g ∈ nbrStab Γ G α) :
    g ∈ nbrStab Γ G β := by
  obtain ⟨i, k, hk, rfl⟩ := S.mem_prod_iff.1 hg
  have h1 : (x ^ i * k) • β = β := mem_nbrStab.1 hgα β S.adj
  have h2 : k • β = β := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer β hk)
  rw [mul_smul, h2] at h1
  rw [S.toXSetup.pow_eq_one_of_smul_eq L i h1, one_mul]
  exact hk

theorem card_eq (L : LocalFacts F) : Nat.card H = pval Γ α * Nat.card (nbrStab Γ G β) := by
  have h1 := Subgroup.relIndex_mul_card (H := MulAction.stabilizer G β) (K := H)
  have h2 : (MulAction.stabilizer G β).relIndex H = pval Γ α := by
    have hsub : (MulAction.stabilizer G β).subgroupOf H = MulAction.stabilizer ↥H β := by
      ext h
      simp [MulAction.mem_stabilizer_iff]
    have horb : MulAction.orbit ↥H β = Γ.neighborSet α := by
      ext γ
      constructor
      · rintro ⟨⟨h, hh⟩, rfl⟩
        exact F.adj_smul_of_mem_stabilizer (S.le_stab hh) S.adj
      · intro hγ
        obtain ⟨i, hi⟩ := L.pow_smul_eq S.mem S.ord S.adj hγ
        exact ⟨⟨x ^ i, Subgroup.pow_mem _ S.x_mem i⟩, hi⟩
    rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer, horb]
    exact Nat.card_coe_set_eq _ ▸ rfl
  rw [h2, inf_comm, S.inf_stab L] at h1
  exact h1.symm

theorem conj_mem_inf (L : LocalFacts F) {h : G} (hh : h ∈ H) {l : G}
    (hl : l ∈ nbrStab Γ G α ⊓ nbrStab Γ G β) : h * l * h⁻¹ ∈ nbrStab Γ G α ⊓ nbrStab Γ G β := by
  have hhα : h ∈ MulAction.stabilizer G α := S.le_stab hh
  have hc : h * l * h⁻¹ ∈ nbrStab Γ G α := F.conj_mem_nbrStab_of_stab hhα hl.1
  exact ⟨hc, S.mem_nbrStab_of_mem L (H.mul_mem (H.mul_mem hh (S.nbrStab_le hl.2)) (H.inv_mem hh))
    hc⟩

theorem inf_eq_ballStab_two (L : LocalFacts F) :
    nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α := by
  refine le_antisymm (fun l hl => ?_) (F.ballStab_two_le_inf S.adj)
  rw [F.mem_ballStab_two_iff]
  refine ⟨hl.1, fun γ hγ => ?_⟩
  obtain ⟨i, hi⟩ := L.pow_smul_eq S.mem S.ord S.adj hγ
  have hxi : x ^ i ∈ H := Subgroup.pow_mem _ S.x_mem i
  have hl' := S.conj_mem_inf L (H.inv_mem hxi) hl
  have := (F.mem_nbrStab_smul_iff (x ^ i) β (h := l)).2 (by simpa using hl'.2)
  rwa [hi] at this

end ProdSetup

end CFSG.Quasithin.Fan86
