module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MElem
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MFacts
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

variable {G : Type} [Group G]

structure M42Sit [Finite G] (β e f : G) (H Λ Δ X : Subgroup G) : Prop where
  cenβ : H ≤ Cen β
  Hnorm : ∀ g ∈ Cen β, ∀ h ∈ H, g * h * g⁻¹ ∈ H
  H3 : ∀ g ∈ Cen β, Nat.Coprime 3 (orderOf g) → g ∈ H
  e_mem : e ∈ H
  f_mem : f ∈ H
  ord_e : orderOf e = 3
  ord_f : orderOf f = 3
  comm : e * f = f * e
  syl : IsSylowOf 3 (Subgroup.closure ({e, f} : Set G)) H
  Λdef : Λ = Lay (H ⊓ Cen e)
  Δdef : Δ = Lay (H ⊓ Cen f)
  f_Λ : f ∈ Λ
  e_Δ : e ∈ Δ
  Λiso : M42GL3 Λ
  Δiso : M42A5 Δ
  Xe : Opp 3 (Cen e ⊓ Cen β) = X
  Xf : Opp 3 (Cen f ⊓ Cen β) = X
  Xodd : Odd (Nat.card X)
  kgn : ∀ M : Subgroup G, M ≤ H → KCore.KGroupNonab InCatalog ↥M

namespace M42Sit

variable [Finite G] {β e f : G} {H Λ Δ X : Subgroup G} (S : M42Sit β e f H Λ Δ X)
include S

theorem coprimeX : Nat.Coprime 3 (Nat.card X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := m42_Opp_coprime 3 (Cen e ⊓ Cen β)
  rwa [S.Xe] at this

theorem X_le_e : X ≤ Cen e ⊓ Cen β := by
  have := m42_Opp_le 3 (Cen e ⊓ Cen β)
  rwa [S.Xe] at this

theorem X_le_f : X ≤ Cen f ⊓ Cen β := by
  have := m42_Opp_le 3 (Cen f ⊓ Cen β)
  rwa [S.Xf] at this

theorem Λ_le : Λ ≤ H ⊓ Cen e := by
  have := m42_Lay_le (H ⊓ Cen e)
  rwa [← S.Λdef] at this

theorem Δ_le : Δ ≤ H ⊓ Cen f := by
  have := m42_Lay_le (H ⊓ Cen f)
  rwa [← S.Δdef] at this

theorem Λ_le_Y : Λ ≤ Cen e ⊓ Cen β := fun x hx =>
  ⟨(S.Λ_le hx).2, S.cenβ (S.Λ_le hx).1⟩

theorem Δ_le_Y : Δ ≤ Cen f ⊓ Cen β := fun x hx =>
  ⟨(S.Δ_le hx).2, S.cenβ (S.Δ_le hx).1⟩

theorem norm_H {g : G} (hg : g ∈ Cen β) : ∀ m, m ∈ H ↔ g * m * g⁻¹ ∈ H := by
  intro m
  refine ⟨S.Hnorm g hg m, fun hm => ?_⟩
  have := S.Hnorm g⁻¹ (Subgroup.inv_mem _ hg) _ hm
  simpa [mul_assoc] using this

theorem fwd_HCen {x g : G} (hg : g ∈ Cen β) (hgx : g ∈ Cen x) {m : G} (hm : m ∈ H ⊓ Cen x) :
    g * m * g⁻¹ ∈ H ⊓ Cen x := by
  refine ⟨S.Hnorm g hg m hm.1, m42_mem_cen ?_⟩
  have hxg : Commute x g := m42_cen_comm hgx
  have hxm : Commute x m := m42_cen_comm hm.2
  exact ((hxg.mul_right hxm).mul_right hxg.inv_right).eq

theorem norm_HCen {x g : G} (hg : g ∈ Cen β) (hgx : g ∈ Cen x) :
    ∀ m, m ∈ H ⊓ Cen x ↔ g * m * g⁻¹ ∈ H ⊓ Cen x := by
  intro m
  refine ⟨S.fwd_HCen hg hgx, fun hm => ?_⟩
  have := S.fwd_HCen (Subgroup.inv_mem _ hg) (Subgroup.inv_mem _ hgx) hm
  simpa [mul_assoc] using this

theorem Λ_conj {g z : G} (hg : g ∈ Cen e ⊓ Cen β) (hz : z ∈ Λ) : g * z * g⁻¹ ∈ Λ := by
  rw [S.Λdef] at hz ⊢
  exact m42_Lay_conj_mem_of_normalizes (S.norm_HCen hg.2 hg.1) hz

theorem Δ_conj {g z : G} (hg : g ∈ Cen f ⊓ Cen β) (hz : z ∈ Δ) : g * z * g⁻¹ ∈ Δ := by
  rw [S.Δdef] at hz ⊢
  exact m42_Lay_conj_mem_of_normalizes (S.norm_HCen hg.2 hg.1) hz

theorem Xe_conj {g z : G} (hg : g ∈ Cen e ⊓ Cen β) (hz : z ∈ X) : g * z * g⁻¹ ∈ X := by
  rw [← S.Xe] at hz ⊢
  exact m42_Opp_conj_mem hg hz

theorem Xf_conj {g z : G} (hg : g ∈ Cen f ⊓ Cen β) (hz : z ∈ X) : g * z * g⁻¹ ∈ X := by
  rw [← S.Xf] at hz ⊢
  exact m42_Opp_conj_mem hg hz

theorem not_dvd_X : ¬ 3 ∣ Nat.card X := fun h => by
  have := Nat.Coprime.eq_one_of_dvd S.coprimeX h
  omega

theorem comm_ΛX : ∀ l ∈ Λ, ∀ x ∈ X, l * x = x * l := by
  haveI : IsSimpleGroup ↥Λ := S.Λiso.simple
  refine m42_comm_of_normal (Y := Cen e ⊓ Cen β) S.Λ_le_Y S.X_le_e
    (fun y hy s hs => S.Λ_conj hy hs) (fun y hy n hn => S.Xe_conj hy hn) ?_
  intro h
  exact S.not_dvd_X (by
    have := Subgroup.orderOf_dvd_natCard X (h S.f_Λ)
    rwa [S.ord_f] at this)

theorem comm_ΔX : ∀ d ∈ Δ, ∀ x ∈ X, d * x = x * d := by
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  refine m42_comm_of_normal (Y := Cen f ⊓ Cen β) S.Δ_le_Y S.X_le_f
    (fun y hy s hs => S.Δ_conj hy hs) (fun y hy n hn => S.Xf_conj hy hn) ?_
  intro h
  exact S.not_dvd_X (by
    have := Subgroup.orderOf_dvd_natCard X (h S.e_Δ)
    rwa [S.ord_e] at this)

theorem H0_cen_le_X {z : G} (hz : z ∈ Opp 3 H) (hzf : z ∈ Cen f) : z ∈ X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Opp 3 H ⊓ Cen f ≤ Opp 3 (Cen f ⊓ Cen β) := by
    refine m42_le_Opp (p := 3) (fun n hn => ⟨hn.2, S.cenβ (m42_Opp_le 3 H hn.1)⟩) ?_ ?_
    · intro h hh n hn
      refine ⟨m42_Opp_conj_mem_of_normalizes (S.norm_H hh.2) hn.1, m42_mem_cen ?_⟩
      have hc : Commute f h := m42_cen_comm hh.1
      have hc2 : Commute f n := m42_cen_comm hn.2
      exact ((hc.mul_right hc2).mul_right hc.inv_right).eq
    · exact (m42_Opp_coprime 3 H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  rw [← S.Xf]
  exact hN ⟨hz, hzf⟩

theorem H0_le_cenΛ (hN : FF79LemmaN) : Opp 3 H ≤ CenS Λ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine hN G (Opp 3 H) Λ f (S.kgn _ (m42_Opp_le 3 H)) S.Λiso ?_ (m42_Opp_coprime 3 H)
    S.f_Λ S.ord_f ?_
  · intro l hl
    exact m42_Opp_normalizes 3 H (S.Λ_le hl).1
  · intro z hz
    have hzX : z ∈ X := S.H0_cen_le_X hz.1 hz.2
    exact m42_mem_cenS fun l hl => S.comm_ΛX l hl z hzX

theorem H0_le_X (hN : FF79LemmaN) : Opp 3 H ≤ X := fun z hz =>
  S.H0_cen_le_X hz (m42_mem_cen (m42_cenS_comm (S.H0_le_cenΛ hN hz) S.f_Λ))

theorem comm_Δ_H0 (hN : FF79LemmaN) : ∀ d ∈ Δ, ∀ z ∈ Opp 3 H, d * z = z * d :=
  fun d hd z hz => S.comm_ΔX d hd z (S.H0_le_X hN hz)

theorem Cen_ne : Cen e ≠ Cen f := by
  intro h
  have : Λ = Δ := by rw [S.Λdef, S.Δdef, h]
  have h1 := S.Λiso.card
  have h2 := S.Δiso.card
  rw [this] at h1
  omega

theorem no_conj : ¬ ∃ g ∈ H, conjBy g (Subgroup.zpowers e) = Subgroup.zpowers f := by
  rintro ⟨g, hg, hgc⟩
  have h1 : Subgroup.zpowers (g * e * g⁻¹) = Subgroup.zpowers f := by
    rw [← hgc]
    exact (MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom e).symm
  have hmem : g * e * g⁻¹ ∈ Subgroup.zpowers f := by
    rw [← h1]; exact Subgroup.mem_zpowers _
  have hcen : Cen (g * e * g⁻¹) = Cen f :=
    m42_cen_eq_of_mem_zpowers (by rw [m42_orderOf_conj, S.ord_e]) S.ord_f hmem
  have hL := m42_Lay_map (MulAut.conj g) (H ⊓ Cen e)
  rw [m42_map_HCen hg e, hcen, ← S.Λdef, ← S.Δdef] at hL
  have hc : Nat.card (Λ.map (MulAut.conj g).toMonoidHom) = Nat.card Λ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hL] at hc
  have h1 := S.Λiso.card
  have h2 := S.Δiso.card
  omega

theorem hint : Subgroup.zpowers e ⊓ Subgroup.zpowers f = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hne
  have hoz : ∀ {w : G} (hw : w ∈ Subgroup.zpowers e) (hne : w ≠ 1), orderOf w = 3 := by
    intro w hw hne
    have hd := Subgroup.orderOf_dvd_natCard _ hw
    rw [Nat.card_zpowers, S.ord_e] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hz3 := hoz hz.1 hne
  have h1 := m42_cen_eq_of_mem_zpowers hz3 S.ord_e hz.1
  have h2 := m42_cen_eq_of_mem_zpowers hz3 S.ord_f hz.2
  exact S.Cen_ne (h1.symm.trans h2)

theorem card_P : Nat.card (Subgroup.closure ({e, f} : Set G)) = 9 :=
  m42_card_pair S.ord_e S.ord_f S.comm S.hint

theorem Δ_sup_H0 (hQ : FF84.LemmaQ) :
    Δ ⊔ Opp 3 H ≤ H ∧ ((Δ ⊔ Opp 3 H).subgroupOf H).Normal := by
  refine hQ G H (Subgroup.closure ({e, f} : Set G)) (Subgroup.zpowers e) (Subgroup.zpowers f)
    Δ (S.kgn H le_rfl) S.syl S.card_P
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    (by rw [Nat.card_zpowers, S.ord_e]) (by rw [Nat.card_zpowers, S.ord_f]) S.hint
    (by rw [m42_cenS_zpowers]; exact S.Δ_le) ?_ S.Δiso.card S.Δiso.simple
    (Subgroup.zpowers_le.mpr S.e_Δ) S.no_conj
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hHC : H ⊓ CenS (Subgroup.zpowers f) = H ⊓ Cen f := by rw [m42_cenS_zpowers]
  have hg : (g : G) ∈ H ⊓ Cen f := hHC ▸ g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [S.Δdef] at hn ⊢
  exact m42_Lay_conj_mem hg hn

end M42Sit

end CFSG.RankThree.PartTwo.Sec21.FF79
