module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MStruct
import CFSG.RankThree.PartTwo.Sec21.Item233TablesBasic
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

variable {G : Type} [Group G]

theorem m42_closure_conj_mem {S : Set G} {g : G}
    (hS : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) :
    ∀ t ∈ Subgroup.closure S, g * t * g⁻¹ ∈ Subgroup.closure S := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem m42_mem_sup_of_comm {A H : Subgroup G} (hc : ∀ a ∈ A, ∀ h ∈ H, a * h = h * a)
    {g : G} (hg : g ∈ A ⊔ H) : ∃ a ∈ A, ∃ h ∈ H, g = a * h := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ h ∈ H, g = a * h}
      mul_mem' := by
        rintro _ _ ⟨a, ha, h, hh, rfl⟩ ⟨a', ha', h', hh', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', h * h', H.mul_mem hh hh', ?_⟩
        have := hc a' ha' h hh
        calc a * h * (a' * h') = a * (h * a') * h' := by simp only [mul_assoc]
          _ = a * (a' * h) * h' := by rw [this]
          _ = a * a' * (h * h') := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, H.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, h, hh, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, h⁻¹, H.inv_mem hh, ?_⟩
        have : Commute a h := hc a ha h hh
        rw [mul_inv_rev]
        exact ((this.inv_inv).symm.eq) }
  have hle : A ⊔ H ≤ S := by
    refine sup_le (fun a ha => ⟨a, ha, 1, H.one_mem, (mul_one a).symm⟩)
      (fun h hh => ⟨1, A.one_mem, h, hh, (one_mul h).symm⟩)
  exact hle hg

theorem m42_comp_le_Lay {H M : Subgroup G} (hMH : M ≤ H) {C : Subgroup ↥H}
    (hC : CFSG.IsComponent C) (hCM : C.map H.subtype ≤ M) : C.map H.subtype ≤ Lay M := by
  let M₁ : Subgroup ↥H := M.subgroupOf H
  have hCM₁ : C ≤ M₁ := fun x hx => Subgroup.mem_subgroupOf.mpr (hCM ⟨x, hx, rfl⟩)
  have hcomp := CFSG.LocalCores.component_overgroup hC hCM₁
  have h1 := Subgroup.map_mono (f := M₁.subtype) (CFSG.LocalCores.component_le_layer hcomp)
  rw [Subgroup.map_subgroupOf_eq_of_le hCM₁] at h1
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  have h3 := map_inSubgroup_layer_of_injective H.subtype_injective M₁
  rw [Subgroup.map_subgroupOf_eq_of_le hMH] at h3
  exact h2.trans (le_of_eq h3)

theorem m42_nonab_of_card {N : Subgroup G} [IsSimpleGroup ↥N] [Finite G]
    (h : ¬ (Nat.card N).Prime) : ∃ a b : ↥N, a * b ≠ b * a := by
  by_contra hcon
  push_neg at hcon
  letI : CommGroup ↥N := { (inferInstance : Group ↥N) with mul_comm := hcon }
  exact h (IsSimpleGroup.prime_card (α := ↥N))

theorem m42_simple_le_Lay {H N : Subgroup G} [Finite G] (hNH : N ≤ H)
    (hn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) [IsSimpleGroup ↥N]
    (hnonab : ∃ a b : ↥N, a * b ≠ b * a) : N ≤ Lay H := by
  obtain ⟨a, b, hab⟩ := hnonab
  have hq : CFSG.IsQuasisimple N :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).1
  refine le_inSubgroup_layer_of_normal hNH (fun h hh => ?_) hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hn h hh x, fun hx => ?_⟩
  have := hn h⁻¹ (H.inv_mem hh) _ hx
  simpa [mul_assoc] using this

namespace M42Sit

variable [Finite G] {β e f : G} {H Λ Δ X : Subgroup G} (S : M42Sit β e f H Λ Δ X)
include S

theorem Δ_nonab : ∃ a b : ↥Δ, a * b ≠ b * a := by
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  refine m42_nonab_of_card ?_
  rw [S.Δiso.card]
  norm_num

theorem Λ_nonab : ∃ a b : ↥Λ, a * b ≠ b * a := by
  haveI : IsSimpleGroup ↥Λ := S.Λiso.simple
  refine m42_nonab_of_card ?_
  rw [S.Λiso.card]
  norm_num

theorem Δ_le_H : Δ ≤ H := fun x hx => (S.Δ_le hx).1

theorem Λ_le_H : Λ ≤ H := fun x hx => (S.Λ_le hx).1

theorem Δ_le_closure3 : Δ ≤ Subgroup.closure {x | x ∈ Δ ∧ orderOf x = 3} := by
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  set T := Subgroup.closure {x | x ∈ Δ ∧ orderOf x = 3} with hT
  have hconj : ∀ g ∈ Δ, ∀ t ∈ T, g * t * g⁻¹ ∈ T := fun g hg =>
    m42_closure_conj_mem fun x hx => Subgroup.subset_closure
      ⟨Δ.mul_mem (Δ.mul_mem hg hx.1) (Δ.inv_mem hg), by rw [m42_orderOf_conj, hx.2]⟩
  let T' : Subgroup ↥Δ := T.subgroupOf Δ
  haveI : T'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconj g.1 g.2 n.1 hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T' with h | h
  · exfalso
    have : (⟨e, S.e_Δ⟩ : ↥Δ) ∈ T' :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨S.e_Δ, S.ord_e⟩)
    rw [h, Subgroup.mem_bot] at this
    have h1 : e = 1 := congrArg Subtype.val this
    have h2 := S.ord_e
    rw [h1, orderOf_one] at h2
    omega
  · intro x hx
    have : (⟨x, hx⟩ : ↥Δ) ∈ T' := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem Δ_inf_H0 : Opp 3 H ⊓ Δ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  rcases m42_simple_inf (S := Δ) (N := Opp 3 H) (fun s hs n hn =>
    ⟨m42_Opp_conj_mem (S.Δ_le_H hs) hn.1, Δ.mul_mem (Δ.mul_mem hs hn.2) (Δ.inv_mem hs)⟩)
    with h | h
  · exact h
  · exfalso
    have := m42_Opp_orderOf 3 (h S.e_Δ)
    rw [S.ord_e] at this
    norm_num at this

theorem Δ_normal (hN : FF79LemmaN) (hQ : FF84.LemmaQ) :
    ∀ h ∈ H, ∀ d ∈ Δ, h * d * h⁻¹ ∈ Δ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hMH, hMn⟩ := S.Δ_sup_H0 hQ
  have key : ∀ h ∈ H, ∀ x ∈ Δ, orderOf x = 3 → h * x * h⁻¹ ∈ Δ := by
    intro h hh x hx hox
    have hy : h * x * h⁻¹ ∈ Δ ⊔ Opp 3 H := by
      have := hMn.conj_mem ⟨x, hMH (Subgroup.mem_sup_left hx)⟩
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hx)) ⟨h, hh⟩
      simpa using Subgroup.mem_subgroupOf.mp this
    obtain ⟨a, ha, z, hz, hyz⟩ := m42_mem_sup_of_comm (S.comm_Δ_H0 hN) hy
    have hord : (h * x * h⁻¹) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (h * x * h⁻¹)
      rwa [m42_orderOf_conj, hox] at this
    rw [hyz] at hord
    have hcz : Commute a z := S.comm_Δ_H0 hN a ha z hz
    rw [hcz.mul_pow] at hord
    have h3 : a ^ 3 ∈ Opp 3 H ⊓ Δ := by
      refine ⟨?_, Δ.pow_mem ha 3⟩
      have : a ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hord
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz 3)
    rw [S.Δ_inf_H0, Subgroup.mem_bot] at h3
    have hz3 : z ^ 3 = 1 := by rw [h3, one_mul] at hord; exact hord
    have hzo : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hcop := m42_Opp_orderOf 3 hz
    have : orderOf z = 1 := by
      have := Nat.Coprime.eq_one_of_dvd hcop.symm (by simpa using hzo)
      simpa using this
    rw [orderOf_eq_one_iff.mp this, mul_one] at hyz
    rw [hyz]; exact ha
  intro h hh d hd
  have := m42_closure_conj_mem (g := h) (S := {x | x ∈ Δ ∧ orderOf x = 3}) (fun x hx =>
    Subgroup.subset_closure ⟨key h hh x hx.1 hx.2, by rw [m42_orderOf_conj, hx.2]⟩) d
    (S.Δ_le_closure3 hd)
  exact ((Subgroup.closure_le Δ).mpr (fun x hx => hx.1)) this


theorem factorization_Δ : (Nat.card Δ).factorization 3 = 1 := by
  rw [S.Δiso.card]; exact m42_fact_fact60

theorem factorization_Λ : (Nat.card Λ).factorization 3 = 1 := by
  rw [S.Λiso.card]; exact m42_fact_fact168

theorem H_split (hN : FF79LemmaN) (hQ : FF84.LemmaQ) :
    ∀ h ∈ H, ∃ k ∈ Δ, ∃ c ∈ H ⊓ Cen e, h = k * c := by
  intro h hh
  have hx : h * e * h⁻¹ ∈ Δ := S.Δ_normal hN hQ h hh e S.e_Δ
  obtain ⟨k, hk, hke⟩ := m42_conj_exact S.factorization_Δ S.Δiso.inv S.e_Δ hx S.ord_e
    (by rw [m42_orderOf_conj, S.ord_e])
  refine ⟨k, hk, k⁻¹ * h, ⟨H.mul_mem (H.inv_mem (S.Δ_le_H hk)) hh, m42_mem_cen ?_⟩, by group⟩
  have : k⁻¹ * h * e * (k⁻¹ * h)⁻¹ = e := by
    have e1 : k⁻¹ * h * e * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * e * h⁻¹) * k := by group
    rw [e1, ← hke]; group
  have h2 : k⁻¹ * h * e = e * (k⁻¹ * h) := by
    calc k⁻¹ * h * e = k⁻¹ * h * e * (k⁻¹ * h)⁻¹ * (k⁻¹ * h) := by group
      _ = e * (k⁻¹ * h) := by rw [this]
  exact h2.symm

theorem comm_ΛΔ (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : ∀ l ∈ Λ, ∀ d ∈ Δ, l * d = d * l :=
  m42_comm_A5_GL3 S.Δiso S.Λiso fun l hl d hd => S.Δ_normal hN hQ l (S.Λ_le_H hl) d hd

theorem Λ_normal (hN : FF79LemmaN) (hQ : FF84.LemmaQ) :
    ∀ h ∈ H, ∀ l ∈ Λ, h * l * h⁻¹ ∈ Λ := by
  intro h hh l hl
  obtain ⟨k, hk, c, hc, rfl⟩ := S.H_split hN hQ h hh
  have hc' : c ∈ Cen e ⊓ Cen β := ⟨hc.2, S.cenβ hc.1⟩
  have h1 := S.Λ_conj hc' hl
  have h2 : k * c * l * (k * c)⁻¹ = k * (c * l * c⁻¹) * k⁻¹ := by group
  rw [h2]
  have hcomm := S.comm_ΛΔ hN hQ _ h1 k hk
  have : k * (c * l * c⁻¹) * k⁻¹ = c * l * c⁻¹ := by
    rw [← hcomm]; group
  rw [this]; exact h1

theorem X_le_H : X ≤ H := by
  intro z hz
  have hc : Nat.Coprime 3 (orderOf z) :=
    S.coprimeX.coprime_dvd_right (Subgroup.orderOf_dvd_natCard X hz)
  exact S.H3 z (S.X_le_f hz).2 hc

theorem X_normal (hN : FF79LemmaN) (hQ : FF84.LemmaQ) :
    ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
  intro h hh x hx
  obtain ⟨k, hk, c, hc, rfl⟩ := S.H_split hN hQ h hh
  have h1 := S.Xe_conj (g := c) ⟨hc.2, S.cenβ hc.1⟩ hx
  have h2 : k * c * x * (k * c)⁻¹ = k * (c * x * c⁻¹) * k⁻¹ := by group
  rw [h2]
  exact S.Xf_conj (S.Δ_le_Y hk) h1

theorem Opp_eq (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Opp 3 H = X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact le_antisymm (S.H0_le_X hN)
    (m42_le_Opp S.X_le_H (S.X_normal hN hQ) S.coprimeX)

theorem Δ_le_Lay (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Δ ≤ Lay H := by
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  exact m42_simple_le_Lay S.Δ_le_H (S.Δ_normal hN hQ) S.Δ_nonab

theorem Λ_le_Lay (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Λ ≤ Lay H := by
  haveI : IsSimpleGroup ↥Λ := S.Λiso.simple
  exact m42_simple_le_Lay S.Λ_le_H (S.Λ_normal hN hQ) S.Λ_nonab

theorem Lay_le (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Lay H ≤ Δ ⊔ Λ := by
  let Δ' : Subgroup ↥H := Δ.subgroupOf H
  haveI : Δ'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using S.Δ_normal hN hQ g.1 g.2 n.1 hn⟩
  have hcomp : ∀ C : Subgroup ↥H, CFSG.IsComponent C → C.map H.subtype ≤ Δ ⊔ Λ := by
    intro C hC
    rcases CFSG.LocalCores.component_subnormal_subgroup hC (Subgroup.Normal.isSubnormal ‹_›)
      with h | h
    · refine le_trans ?_ (le_sup_left : Δ ≤ Δ ⊔ Λ)
      calc C.map H.subtype ≤ Δ'.map H.subtype := Subgroup.map_mono h
        _ = Δ := Subgroup.map_subgroupOf_eq_of_le S.Δ_le_H
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hCM : C.map H.subtype ≤ H ⊓ Cen e := by
        rintro _ ⟨c, hc, rfl⟩
        refine ⟨c.2, m42_mem_cen ?_⟩
        have := Subgroup.mem_centralizer_iff.mp (hle hc) ⟨e, S.e_mem⟩
          (Subgroup.mem_subgroupOf.mpr S.e_Δ)
        have h3 := congrArg Subtype.val this
        exact h3
      refine le_trans (m42_comp_le_Lay (le_refl _ |>.trans' inf_le_left) hC hCM) ?_
      rw [← S.Λdef]
      exact le_sup_right
  have : layer ↥H ≤ (Δ ⊔ Λ).comap H.subtype :=
    sSup_le fun C hC => fun x hx => hcomp C hC ⟨x, hx, rfl⟩
  exact (Subgroup.map_mono this).trans (Subgroup.map_comap_le _ _)

theorem Lay_eq (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Lay H = Δ ⊔ Λ :=
  le_antisymm (S.Lay_le hN hQ) (sup_le (S.Δ_le_Lay hN hQ) (S.Λ_le_Lay hN hQ))

theorem Λ_inf_Δ (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Δ ⊓ Λ = ⊥ := by
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  rcases m42_simple_inf (S := Δ) (N := Λ) (fun s hs n hn => by
    have := S.comm_ΛΔ hN hQ n hn.1 s hs
    have e1 : s * n * s⁻¹ = n := by rw [← this]; group
    rw [e1]; exact hn) with h | h
  · rw [inf_comm]; exact h
  · exfalso
    have := Subgroup.card_dvd_of_le h
    rw [S.Δiso.card, S.Λiso.card] at this
    omega

theorem Δ_le_cenΛ (hN : FF79LemmaN) (hQ : FF84.LemmaQ) : Δ ≤ CenS Λ :=
  fun d hd => m42_mem_cenS fun l hl => S.comm_ΛΔ hN hQ l hl d hd

theorem H_eq_cen_Lay (hN : FF79LemmaN) (hQ : FF84.LemmaQ) :
    setMul (H ⊓ CenS (Subgroup.closure ({e, f} : Set G))) (Lay H) = H := by
  have hLayH : Lay H ≤ H := m42_Lay_le H
  ext h
  constructor
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact H.mul_mem hc.1 (hLayH hy)
  · intro hh
    obtain ⟨k₁, hk₁, c₁, hc₁, rfl⟩ := S.H_split hN hQ h hh
    have hfc : c₁ * f * c₁⁻¹ ∈ Λ := S.Λ_normal hN hQ c₁ hc₁.1 f S.f_Λ
    obtain ⟨k₂, hk₂, hk₂f⟩ := m42_conj_exact S.factorization_Λ S.Λiso.inv S.f_Λ hfc S.ord_f
      (by rw [m42_orderOf_conj, S.ord_f])
    have hk₂e : k₂ * e = e * k₂ := (m42_cen_comm (S.Λ_le hk₂).2).symm
    have hc₂H : k₂⁻¹ * c₁ ∈ H := H.mul_mem (H.inv_mem (S.Λ_le_H hk₂)) hc₁.1
    have hc₂e : k₂⁻¹ * c₁ * e = e * (k₂⁻¹ * c₁) := by
      have hce : c₁ * e = e * c₁ := (m42_cen_comm hc₁.2).symm
      calc k₂⁻¹ * c₁ * e = k₂⁻¹ * (e * c₁) := by rw [mul_assoc, hce]
        _ = (k₂⁻¹ * e) * c₁ := by rw [← mul_assoc]
        _ = (e * k₂⁻¹) * c₁ := by
          congr 1
          have : k₂⁻¹ * e = e * k₂⁻¹ := by
            calc k₂⁻¹ * e = k₂⁻¹ * (e * k₂) * k₂⁻¹ := by group
              _ = k₂⁻¹ * (k₂ * e) * k₂⁻¹ := by rw [hk₂e]
              _ = e * k₂⁻¹ := by group
          exact this
        _ = e * (k₂⁻¹ * c₁) := by rw [mul_assoc]
    have hc₂f : k₂⁻¹ * c₁ * f = f * (k₂⁻¹ * c₁) := by
      have : k₂⁻¹ * c₁ * f * (k₂⁻¹ * c₁)⁻¹ = f := by
        have e1 : k₂⁻¹ * c₁ * f * (k₂⁻¹ * c₁)⁻¹ = k₂⁻¹ * (c₁ * f * c₁⁻¹) * k₂ := by group
        rw [e1, ← hk₂f]; group
      calc k₂⁻¹ * c₁ * f = k₂⁻¹ * c₁ * f * (k₂⁻¹ * c₁)⁻¹ * (k₂⁻¹ * c₁) := by group
        _ = f * (k₂⁻¹ * c₁) := by rw [this]
    set c₂ := k₂⁻¹ * c₁ with hc₂
    have hc₂P : c₂ ∈ CenS (Subgroup.closure ({e, f} : Set G)) := by
      rw [m42_cenS_closure_pair]
      exact ⟨m42_mem_cen hc₂e.symm, m42_mem_cen hc₂f.symm⟩
    have hLk : k₁ * k₂ ∈ Lay H :=
      (Lay H).mul_mem (S.Δ_le_Lay hN hQ hk₁) (S.Λ_le_Lay hN hQ hk₂)
    refine ⟨c₂, ⟨hc₂H, hc₂P⟩, c₂⁻¹ * (k₁ * k₂) * c₂, ?_, ?_⟩
    · have := m42_Lay_conj_mem (H.inv_mem hc₂H) hLk
      simpa using this
    · have : c₂ = k₂⁻¹ * c₁ := hc₂
      calc k₁ * c₁ = k₁ * k₂ * (k₂⁻¹ * c₁) := by group
        _ = c₂ * (c₂⁻¹ * (k₁ * k₂) * c₂) := by rw [hc₂]; group

end M42Sit

end CFSG.RankThree.PartTwo.Sec21.FF79
