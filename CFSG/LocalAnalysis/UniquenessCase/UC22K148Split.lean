module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sec
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.RankThree.FFModules.FixSubConj
import CFSG.Quasithin.Background.G119Group2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped Pointwise

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {N : Subgroup G} {a : G}

theorem cenOn_commOn_normal (hN : N.Normal) : (cenOn ρ ⊤ (commOn ρ N ⊤)).Normal := by
  have hNN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hN]
  refine ⟨fun k hk g => ⟨Subgroup.mem_top _, fun x hx => ?_⟩⟩
  rw [glRep_mul_apply, glRep_mul_apply,
    hk.2 _ ((invariant_commOn_top hNN).2 g⁻¹ (Subgroup.mem_top _) x hx), glRep_apply_inv]

theorem inf_cenOn_commOn_eq_bot (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1) :
    N ⊓ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun n hn => hfa n hn.1 hn.2.2

theorem exists_eq_apply_of_mem_sup (hN : N.Normal) {g : G}
    (hg : g ∈ N ⊔ cenOn ρ ⊤ (commOn ρ N ⊤)) : ∃ n ∈ N, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ n x := by
  haveI := hN
  have h : g ∈ (N : Set G) * (cenOn ρ ⊤ (commOn ρ N ⊤) : Set G) := by
    rw [← Subgroup.normal_mul]
    exact hg
  obtain ⟨n, hn, k, hk, rfl⟩ := h
  exact ⟨n, hn, fun x hx => by rw [glRep_mul_apply, hk.2 x hx]⟩

theorem notMem_sup_cenOn_commOn (hN : N.Normal)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x) :
    a ∉ N ⊔ cenOn ρ ⊤ (commOn ρ N ⊤) := fun ha => by
  obtain ⟨n, hn, h⟩ := exists_eq_apply_of_mem_sup hN ha
  exact hout n hn h

theorem inf_sup_zpowers_eq_bot (hN : N.Normal) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x) :
    N ⊓ (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊥ := by
  have hK := cenOn_commOn_normal (ρ := ρ) hN
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  rcases CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers ha2
    (fun k hk => hK.conj_mem k hk a) hg.2 with h | h
  · exact hfa g hg.1 h.2
  · refine absurd ?_ (notMem_sup_cenOn_commOn hN hout)
    have e : a = g⁻¹ * (g * a) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (N.inv_mem hg.1)) (Subgroup.mem_sup_right h)

theorem sup_sup_zpowers_eq_top
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x) :
    N ⊔ (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨h, hh, hgh⟩ := hact g
  have hk : h⁻¹ * g ∈ cenOn ρ ⊤ (commOn ρ N ⊤) :=
    ⟨Subgroup.mem_top _, fun x hx => by rw [glRep_mul_apply, hgh x hx, glRep_inv_apply]⟩
  have e : g = h * (h⁻¹ * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ (sup_le_sup_left le_sup_right N hh)
    (Subgroup.mem_sup_right (Subgroup.mem_sup_left hk))

theorem split_or_pCore_eq_bot (hO : CFSG.pCore 2 G = ⊥) (hN : N.Normal) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x) :
    (∃ r : G, r * r = 1 ∧ r ∈ cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a ∧
      r ∉ N ⊔ cenOn ρ ⊤ (commOn ρ N ⊤) ∧ (N ⊔ Subgroup.zpowers r).Normal ∧
      (N ⊔ Subgroup.zpowers r) ⊓ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊥ ∧
      (N ⊔ Subgroup.zpowers r) ⊔ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊤ ∧
      ∀ m ∈ N ⊔ Subgroup.zpowers r, ∀ k ∈ cenOn ρ ⊤ (commOn ρ N ⊤), m * k = k * m) ∨
    CFSG.pCore 2 ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊥ := by
  set K := cenOn ρ ⊤ (commOn ρ N ⊤)
  have hK : K.Normal := cenOn_commOn_normal hN
  have hNK : N ⊓ K = ⊥ := inf_cenOn_commOn_eq_bot hfa
  have hcomm : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n := fun n hn k hk =>
    Subgroup.commute_of_normal_of_disjoint N K hN hK (disjoint_iff.2 hNK) n k hn hk
  have hsup := sup_sup_zpowers_eq_top hact
  have haNK : a ∉ N ⊔ K := notMem_sup_cenOn_commOn hN hout
  set R := (CFSG.pCore 2 ↥(K ⊔ Subgroup.zpowers a)).map (K ⊔ Subgroup.zpowers a).subtype
  have hRn : ∀ x ∈ R, ∀ k ∈ K ⊔ Subgroup.zpowers a, k * x * k⁻¹ ∈ R := by
    rintro _ ⟨x, hx, rfl⟩ k hk
    exact ⟨⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem x hx _, rfl⟩
  have hRK : R ⊓ K = ⊥ := by
    have hnorm : (R ⊓ K).Normal := ⟨fun x hx g => by
      have hg : g ∈ (N : Set G) * ((K ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
        haveI := hN
        rw [← Subgroup.normal_mul, hsup]
        exact Subgroup.mem_top g
      obtain ⟨n, hn, k, hk, rfl⟩ := hg
      have h1 : k * x * k⁻¹ ∈ R ⊓ K := ⟨hRn x hx.1 k hk, hK.conj_mem x hx.2 k⟩
      have h2 : n * k * x * (n * k)⁻¹ = n * (k * x * k⁻¹) * n⁻¹ := by group
      rw [h2, hcomm n hn _ h1.2, mul_inv_cancel_right]
      exact h1⟩
    have hp : IsPGroup 2 ↥(R ⊓ K) :=
      (CFSG.pCore_isPGroup.map (K ⊔ Subgroup.zpowers a).subtype).to_le inf_le_left
    have hle : R ⊓ K ≤ CFSG.pCore 2 G :=
      le_sSup (s := {M : Subgroup G | M.Normal ∧ IsPGroup 2 M}) ⟨hnorm, hp⟩
    rw [hO] at hle
    exact le_bot_iff.1 hle
  by_cases hR : R = ⊥
  · exact Or.inr ((Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).1 hR)
  refine Or.inl ?_
  obtain ⟨r, hrR, hr1⟩ := (Subgroup.bot_or_exists_ne_one R).resolve_left hR
  have hmemRK : ∀ x ∈ R, x ∈ K → x = 1 := fun x hxR hxK => by
    have h : x ∈ R ⊓ K := ⟨hxR, hxK⟩
    rwa [hRK, Subgroup.mem_bot] at h
  have hrK₀ : r ∈ K ⊔ Subgroup.zpowers a := Subgroup.map_subtype_le _ hrR
  have hraK : r * a ∈ K := (CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers ha2
    (fun k hk => hK.conj_mem k hk a) hrK₀).resolve_left fun h => hr1 (hmemRK r hrR h)
  have hr2 : r * r = 1 := hmemRK _ (R.mul_mem hrR hrR) (by
    have e : r * r = r * a * (a * (r * a) * a⁻¹) := by
      calc r * r = r * (a * a) * r := by rw [ha2, mul_one]
        _ = r * a * (a * (r * a) * a⁻¹) := by group
    rw [e]
    exact K.mul_mem hraK (hK.conj_mem _ hraK a))
  have hrc : ∀ k ∈ K, r * k = k * r := fun k hk => by
    have h1 : r * k * r⁻¹ * k⁻¹ ∈ R := by
      have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
      rw [e]
      exact R.mul_mem hrR (hRn _ (R.inv_mem hrR) k (Subgroup.mem_sup_left hk))
    have h3 := hmemRK _ h1 (K.mul_mem (hK.conj_mem k hk r) (K.inv_mem hk))
    calc r * k = r * k * r⁻¹ * k⁻¹ * (k * r) := by group
      _ = k * r := by rw [h3, one_mul]
  have hrNK : r ∉ N ⊔ K := fun h => haNK (by
    have e : a = r⁻¹ * (r * a) := by group
    rw [e]
    exact (N ⊔ K).mul_mem ((N ⊔ K).inv_mem h) (Subgroup.mem_sup_right hraK))
  have hMK : (N ⊔ Subgroup.zpowers r) ⊓ K = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    rcases CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers hr2
      (fun n hn => hN.conj_mem n hn r) hg.1 with h | h
    · have h' : g ∈ N ⊓ K := ⟨h, hg.2⟩
      rwa [hNK, Subgroup.mem_bot] at h'
    · refine absurd ?_ hrNK
      have e : r = g⁻¹ * (g * r) := by group
      rw [e]
      exact (N ⊔ K).mul_mem ((N ⊔ K).inv_mem (Subgroup.mem_sup_right hg.2))
        (Subgroup.mem_sup_left h)
  have hMKsup : (N ⊔ Subgroup.zpowers r) ⊔ K = ⊤ := by
    refine eq_top_iff.2 (hsup ▸ sup_le (le_sup_left.trans le_sup_left) (sup_le le_sup_right ?_))
    refine Subgroup.zpowers_le.2 ?_
    have e : a = r⁻¹ * (r * a) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers r)))) (Subgroup.mem_sup_right hraK)
  have hMc : ∀ m ∈ N ⊔ Subgroup.zpowers r, ∀ k ∈ K, m * k = k * m := by
    have hle : N ⊔ Subgroup.zpowers r ≤ Subgroup.centralizer (K : Set G) := sup_le
      (fun n hn => Subgroup.mem_centralizer_iff.2 fun k hk => (hcomm n hn k hk).symm)
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun k hk => (hrc k hk).symm))
    exact fun m hm k hk => (Subgroup.mem_centralizer_iff.1 (hle hm) k hk).symm
  have hMn : (N ⊔ Subgroup.zpowers r).Normal := ⟨fun x hx g => by
    have hg : g ∈ ((N ⊔ Subgroup.zpowers r : Subgroup G) : Set G) * (K : Set G) := by
      haveI := hK
      rw [← Subgroup.mul_normal, hMKsup]
      exact Subgroup.mem_top g
    obtain ⟨m, hm, k, hk, rfl⟩ := hg
    have h2 : m * k * x * (m * k)⁻¹ = m * (k * x * k⁻¹) * m⁻¹ := by group
    rw [h2, ← hMc x hx k hk, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hx) (Subgroup.inv_mem _ hm)⟩
  exact ⟨r, hr2, hrK₀, hrNK, hMn, hMK, hMKsup, hMc⟩

private theorem commOn_closure_le {s : Set G} {S : Submodule (ZMod 2) V}
    (h : ∀ g ∈ s, ∀ v, ρ g v - v ∈ S) : commOn ρ (Subgroup.closure s) ⊤ ≤ S := by
  have key : ∀ g ∈ Subgroup.closure s, ∀ v, ρ g v - v ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => intro v; simp
    | mul x y _ _ hx hy =>
      intro v
      have e : ρ (x * y) v - v = (ρ x (ρ y v) - ρ y v) + (ρ y v - v) := by
        rw [map_mul, Module.End.mul_apply]
        abel
      rw [e]
      exact add_mem (hx _) (hy _)
    | inv x _ hx =>
      intro v
      have e : ρ x⁻¹ v - v = -(ρ x (ρ x⁻¹ v) - ρ x⁻¹ v) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        abel
      rw [e]
      exact neg_mem (hx _)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, v, -, rfl⟩
  exact key g hg v

theorem commOn_sup_zpowers_le (hN : N.Normal) (hcod : commOn ρ N ⊤ ⊔ fixSub ρ N = ⊤) {r : G}
    (hr : r * r = 1) :
    commOn ρ (N ⊔ Subgroup.zpowers r) ⊤ ≤ commOn ρ N ⊤ ⊔ fixSub ρ (N ⊔ Subgroup.zpowers r) := by
  have hM : N ⊔ Subgroup.zpowers r = Subgroup.closure ((N : Set G) ∪ {r}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  have hNN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hN]
  conv_lhs => rw [hM]
  refine commOn_closure_le fun g hg v => ?_
  rcases hg with hg | hg
  · exact Submodule.mem_sup_left (sub_mem_commOn hg Submodule.mem_top)
  have hgr : g = r := hg
  rw [hgr]
  have hv : v ∈ commOn ρ N ⊤ ⊔ fixSub ρ N := by
    rw [hcod]
    exact Submodule.mem_top
  obtain ⟨x, hx, e, he, rfl⟩ := Submodule.mem_sup.1 hv
  have hx' : ρ r x - x ∈ commOn ρ N ⊤ :=
    sub_mem ((invariant_commOn_top hNN).2 r (Subgroup.mem_top r) x hx) hx
  have he' : ρ r e - e ∈ fixSub ρ (N ⊔ Subgroup.zpowers r) := by
    rw [fixSub_sup]
    refine ⟨sub_mem (rep_apply_mem_fixSub_of_normal ρ hN r he) he, mem_fixSub_zpowers.2 ?_⟩
    rw [map_sub, ← glRep_mul_apply, hr, map_one, Module.End.one_apply, ZModModule.sub_eq_add,
      ZModModule.sub_eq_add, add_comm]
  have e' : ρ r (x + e) - (x + e) = (ρ r x - x) + (ρ r e - e) := by
    rw [map_add]
    abel
  rw [e']
  exact Submodule.add_mem_sup hx' he'

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
