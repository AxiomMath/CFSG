module

public import CFSG.Quasithin.MS93.S46R468B3

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section General

variable {𝔾 : Type*} [Group 𝔾]

theorem conj_eq_of_mem_normalizer_of_card_two {P : Subgroup 𝔾} (hP : Nat.card P = 2) {r p : 𝔾}
    (hr : r ∈ Subgroup.normalizer (P : Set 𝔾)) (hp : p ∈ P) : r * p * r⁻¹ = p := by
  by_cases hp1 : p = 1
  · rw [hp1, mul_one, mul_inv_cancel]
  have hmem : r * p * r⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hr p).mp hp
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  have h1 : (⟨r * p * r⁻¹, hmem⟩ : P) = y := hy _ fun h => hp1 (by
    have h' : r * p * r⁻¹ = 1 := congrArg Subtype.val h
    calc p = r⁻¹ * (r * p * r⁻¹) * r := by group
      _ = 1 := by rw [h']; group)
  have h2 : (⟨p, hp⟩ : P) = y := hy _ fun h => hp1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem commutatorElement_mul_right' (a b c : 𝔾) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]; group

theorem le_of_commute_commutator {A B K S₁ S₂ : Subgroup 𝔾}
    (hKA : K ≤ Subgroup.normalizer (A : Set 𝔾)) (hKB : K ≤ Subgroup.normalizer (B : Set 𝔾))
    (hK : K ≤ S₁ ⊔ S₂) (hS₁ : S₁ ≤ K) (hS₂ : S₂ ≤ K)
    (h₁ : ∀ r ∈ S₁, ∀ v ∈ B, ∀ u ∈ A, u * ⁅v, r⁆ = ⁅v, r⁆ * u)
    (h₂ : ∀ r ∈ S₂, ∀ v ∈ B, ∀ u ∈ A, u * ⁅v, r⁆ = ⁅v, r⁆ * u) :
    ∀ r ∈ K, ∀ v ∈ B, ∀ u ∈ A, u * ⁅v, r⁆ = ⁅v, r⁆ * u := by
  let S : Subgroup 𝔾 :=
    { carrier := {r | r ∈ K ∧ ∀ v ∈ B, ∀ u ∈ A, u * ⁅v, r⁆ = ⁅v, r⁆ * u}
      one_mem' := ⟨K.one_mem, fun v _ u _ => by rw [commutatorElement_one_right]; group⟩
      mul_mem' := by
        rintro r₁ r₂ ⟨hr₁, hc₁⟩ ⟨hr₂, hc₂⟩
        refine ⟨K.mul_mem hr₁ hr₂, fun v hv u hu => ?_⟩
        have hv' : r₁ * v * r₁⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hKB hr₁) v).mp hv
        have hu' : r₁⁻¹ * u * r₁⁻¹⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (hKA (K.inv_mem hr₁)) u).mp hu
        have e1 : ⁅v, r₁ * r₂⁆ = ⁅v, r₁⁆ * (r₁ * ⁅v, r₂⁆ * r₁⁻¹) := by
          simp only [commutatorElement_def]; group
        have hc : u * (r₁ * ⁅v, r₂⁆ * r₁⁻¹) = (r₁ * ⁅v, r₂⁆ * r₁⁻¹) * u := by
          have h := hc₂ v hv _ hu'
          calc u * (r₁ * ⁅v, r₂⁆ * r₁⁻¹)
              = r₁ * ((r₁⁻¹ * u * r₁⁻¹⁻¹) * ⁅v, r₂⁆) * r₁⁻¹ := by group
            _ = r₁ * (⁅v, r₂⁆ * (r₁⁻¹ * u * r₁⁻¹⁻¹)) * r₁⁻¹ := by rw [h]
            _ = (r₁ * ⁅v, r₂⁆ * r₁⁻¹) * u := by group
        rw [e1, ← mul_assoc, hc₁ v hv u hu, mul_assoc, hc, ← mul_assoc]
      inv_mem' := by
        rintro r ⟨hr, hc⟩
        refine ⟨K.inv_mem hr, fun v hv u hu => ?_⟩
        have hu' : r * u * r⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hr) u).mp hu
        have e1 : ⁅v, r⁻¹⁆ = r⁻¹ * ⁅v, r⁆⁻¹ * r := by
          simp only [commutatorElement_def]; group
        have h := hc v hv _ hu'
        have h' : (r * u * r⁻¹) * ⁅v, r⁆⁻¹ = ⁅v, r⁆⁻¹ * (r * u * r⁻¹) :=
          (show Commute (r * u * r⁻¹) ⁅v, r⁆ from h).inv_right
        rw [e1]
        calc u * (r⁻¹ * ⁅v, r⁆⁻¹ * r) = r⁻¹ * ((r * u * r⁻¹) * ⁅v, r⁆⁻¹) * r := by group
          _ = r⁻¹ * (⁅v, r⁆⁻¹ * (r * u * r⁻¹)) * r := by rw [h']
          _ = r⁻¹ * ⁅v, r⁆⁻¹ * r * u := by group }
  have hle : S₁ ⊔ S₂ ≤ S :=
    sup_le (fun r hr => ⟨hS₁ hr, h₁ r hr⟩) (fun r hr => ⟨hS₂ hr, h₂ r hr⟩)
  exact fun r hr => (hle (hK hr)).2

theorem commutator_mem_of_le_closure {V B K : Subgroup 𝔾} {s : Set 𝔾}
    (hKB : K ≤ Subgroup.normalizer (B : Set 𝔾)) (hK : K ≤ Subgroup.closure s) (hs : s ⊆ K)
    (h : ∀ r ∈ s, ∀ v ∈ V, ⁅v, r⁆ ∈ B) : ∀ r ∈ K, ∀ v ∈ V, ⁅v, r⁆ ∈ B := by
  let S : Subgroup 𝔾 :=
    { carrier := {r | r ∈ K ∧ ∀ v ∈ V, ⁅v, r⁆ ∈ B}
      one_mem' := ⟨K.one_mem, fun v _ => by rw [commutatorElement_one_right]; exact B.one_mem⟩
      mul_mem' := by
        rintro r₁ r₂ ⟨hr₁, hc₁⟩ ⟨hr₂, hc₂⟩
        refine ⟨K.mul_mem hr₁ hr₂, fun v hv => ?_⟩
        have e1 : ⁅v, r₁ * r₂⁆ = ⁅v, r₁⁆ * (r₁ * ⁅v, r₂⁆ * r₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact B.mul_mem (hc₁ v hv)
          ((Subgroup.mem_normalizer_iff.mp (hKB hr₁) _).mp (hc₂ v hv))
      inv_mem' := by
        rintro r ⟨hr, hc⟩
        refine ⟨K.inv_mem hr, fun v hv => ?_⟩
        have e1 : ⁅v, r⁻¹⁆ = r⁻¹ * ⁅v, r⁆⁻¹ * r⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (hKB (K.inv_mem hr)) _).mp (B.inv_mem (hc v hv)) }
  have hle : Subgroup.closure s ≤ S := (Subgroup.closure_le S).mpr fun r hr => ⟨hs hr, h r hr⟩
  exact fun r hr => (hle (hK hr)).2

theorem le_closure_of_relIndex_eq_two {Q K : Subgroup 𝔾} (hQK : Q ≤ K) (h2 : Q.relIndex K = 2)
    {y : 𝔾} (hyK : y ∈ K) (hyQ : y ∉ Q) : K ≤ Subgroup.closure ((Q : Set 𝔾) ∪ {y}) := by
  set R := Subgroup.closure ((Q : Set 𝔾) ∪ {y}) with hRdef
  have hQR : Q ≤ R := fun q hq => Subgroup.subset_closure (Or.inl hq)
  have hyR : y ∈ R := Subgroup.subset_closure (Or.inr rfl)
  have hRK : R ≤ K := (Subgroup.closure_le K).mpr fun r hr => by
    rcases hr with hr | hr
    · exact hQK hr
    · rw [Set.mem_singleton_iff.mp hr]; exact hyK
  have hmul := Subgroup.relIndex_mul_relIndex Q (R ⊓ K) K (le_inf hQR hQK) inf_le_right
  have hne : Q.relIndex (R ⊓ K) ≠ 1 := fun h1 =>
    hyQ (Subgroup.relIndex_eq_one.mp h1 ⟨hyR, hyK⟩)
  have h1 : (R ⊓ K).relIndex K = 1 := by
    rw [h2] at hmul
    have hpos : (R ⊓ K).relIndex K ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmul; omega
    rcases Nat.lt_or_ge (Q.relIndex (R ⊓ K)) 2 with hlt | hge
    · interval_cases h : Q.relIndex (R ⊓ K)
      · rw [zero_mul] at hmul; omega
      · exact absurd rfl hne
    · nlinarith [Nat.pos_of_ne_zero hpos]
  exact fun k hk => (Subgroup.relIndex_eq_one.mp h1 hk).1

end General

section Amalgam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commute_vv_commutator_vv_ptQ (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {x k m : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxk : (puAmalgam c.pu.le).treeGraph.Adj x k)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x k ≠ Usup _ x m) {u v r : (puAmalgam c.pu.le).Universal}
    (hu : u ∈ Vv (puAmalgam c.pu.le) k) (hv : v ∈ Vv (puAmalgam c.pu.le) m)
    (hr : r ∈ ptQ (puAmalgam c.pu.le) x (Usup _ x k ⊓ Usup _ x m)) :
    u * ⁅v, r⁆ = ⁅v, r⁆ * u := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have h464' := h464 G M T L F φ c
  set P := Usup (puAmalgam c.pu.le) x k ⊓ Usup _ x m with hPdef
  have hPc : Nat.card P = 2 := by rw [card_usup_inf_usup h464 h465 c hx hxk hxm hne, hq]
  have hk : ¬ IsMVtx (puAmalgam c.pu.le) k := (isMVtx_iff_of_adj _ hxk).mp hx
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hVk := I466b.vv_le_vv_of_adj c.pu hx hxk
  have hVm := I466b.vv_le_vv_of_adj c.pu hx hxm
  refine le_of_commute_commutator (A := Vv _ k) (B := Vv _ m) (K := ptQ _ x P)
    (S₁ := Qv _ k ⊓ ptQ _ x P) (S₂ := Qv _ m ⊓ ptQ _ x P)
    (ptQ_le_normalizer_vv h464 h465 h466a c hx hxk inf_le_left)
    (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm inf_le_right)
    (ptQ_le_sup_qv_inf h464 h465 h466a c hx hxk hxm hne rfl) inf_le_right inf_le_right
    ?_ ?_ r hr v hv u hu
  · rintro r ⟨hrk, hrP⟩ v hv u hu
    have hv' : r * v * r⁻¹ ∈ Vv (puAmalgam c.pu.le) m :=
      (Subgroup.mem_normalizer_iff.mp
        (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm inf_le_right hrP) v).mp hv
    have e0 : ⁅v, r⁆ = v * (r * v * r⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    have hd : (puAmalgam c.pu.le).treeGraph.dist k m ≤ 2 := by
      have h1 := dist_triangle (puAmalgam c.pu.le) k x m
      rw [tdist_comm (puAmalgam c.pu.le) k x, dist_eq_one_of_adj _ hxk,
        dist_eq_one_of_adj _ hxm] at h1
      exact h1
    have hz : ⁅u, r⁆ ∈ ZM (puAmalgam c.pu.le) x :=
      zh_le_zm _ hxk (commutator_vv_qv_le_zh c.pu h464' hk
        (Subgroup.commutator_mem_commutator hu hrk))
    have hc₁ : ⁅u, v⁆ ∈ ZH (puAmalgam c.pu.le) k ⊓ ZH _ m :=
      commutator_vv_vv_le_zh_inf h464 c hk hm hd (Subgroup.commutator_mem_commutator hu hv)
    have hc₁x : ⁅u, v⁆ ∈ ZM (puAmalgam c.pu.le) x := zh_le_zm _ hxk hc₁.1
    have hc₁P : ⁅u, v⁆ ∈ P ⊔ Zloc c.pu.le L x := by
      rw [← zh_inf_zh_eq h464 h465 c hx hxk hxm]; exact hc₁
    have hrs : r ∈ stab (puAmalgam c.pu.le) x := (mem_ptQ.mp hrP).1
    have hcen : P ⊔ Zloc c.pu.le L x ≤ Subgroup.centralizer ({r} : Set _) := by
      refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
        (fun z hz => Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
      · rw [Set.mem_singleton_iff.mp hg]
        have := conj_eq_of_mem_normalizer_of_card_two hPc (mem_ptQ.mp hrP).2.1 hp
        calc r * p = r * p * r⁻¹ * r := by group
          _ = p * r := by rw [this]
      · rw [Set.mem_singleton_iff.mp hg]
        exact Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hx hz) r hrs
    have hrc : r * ⁅u, v⁆ * r⁻¹ = ⁅u, v⁆ := by
      have := Subgroup.mem_centralizer_iff.mp (hcen hc₁P) r rfl
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
    have hzu : Commute ⁅u, r⁆ u := commute_zm_vv c.pu hb hx hz (hVk hu)
    have hzv' : Commute ⁅u, r⁆ (r * v * r⁻¹) := commute_zm_vv c.pu hb hx hz (hVm hv')
    have hcv : Commute ⁅u, v⁆ v := commute_zm_vv c.pu hb hx hc₁x (hVm hv)
    have hcv' : Commute ⁅u, v⁆ (r * v * r⁻¹) := commute_zm_vv c.pu hb hx hc₁x (hVm hv')
    have e4 : r * u * r⁻¹ = ⁅u, r⁆⁻¹ * u := by rw [commutatorElement_def]; group
    have hzw : Commute ⁅u, r⁆ (u * (r * v * r⁻¹) * u⁻¹) :=
      (hzu.mul_right hzv').mul_right hzu.inv_right
    have e3 : ⁅u, r * v * r⁻¹⁆ = ⁅u, v⁆ := by
      calc ⁅u, r * v * r⁻¹⁆
          = ⁅u, r⁆⁻¹ * ((u * (r * v * r⁻¹) * u⁻¹) * ⁅u, r⁆) * (r * v * r⁻¹)⁻¹ := by
            rw [← hzw.eq, commutatorElement_def]; group
        _ = ⁅⁅u, r⁆⁻¹ * u, r * v * r⁻¹⁆ := by rw [commutatorElement_def]; group
        _ = ⁅r * u * r⁻¹, r * v * r⁻¹⁆ := by rw [e4]
        _ = r * ⁅u, v⁆ * r⁻¹ := by simp only [commutatorElement_def]; group
        _ = ⁅u, v⁆ := hrc
    have huv : u * v * u⁻¹ = ⁅u, v⁆ * v := by rw [commutatorElement_def]; group
    have huv' : u * (r * v * r⁻¹) * u⁻¹ = ⁅u, v⁆ * (r * v * r⁻¹) := by
      rw [← e3, commutatorElement_def]; group
    have hcw : Commute ⁅u, v⁆ (v * (r * v * r⁻¹)⁻¹) := hcv.mul_right hcv'.inv_right
    rw [e0]
    calc u * (v * (r * v * r⁻¹)⁻¹)
        = (u * v * u⁻¹) * (u * (r * v * r⁻¹) * u⁻¹)⁻¹ * u := by group
      _ = (⁅u, v⁆ * v) * (⁅u, v⁆ * (r * v * r⁻¹))⁻¹ * u := by rw [huv, huv']
      _ = (⁅u, v⁆ * (v * (r * v * r⁻¹)⁻¹)) * ⁅u, v⁆⁻¹ * u := by group
      _ = ((v * (r * v * r⁻¹)⁻¹) * ⁅u, v⁆) * ⁅u, v⁆⁻¹ * u := by rw [hcw.eq]
      _ = (v * (r * v * r⁻¹)⁻¹) * u := by group
  · rintro r ⟨hrm, -⟩ v hv u hu
    have hz : ⁅v, r⁆ ∈ ZM (puAmalgam c.pu.le) x :=
      zh_le_zm _ hxm (commutator_vv_qv_le_zh c.pu h464' hm
        (Subgroup.commutator_mem_commutator hv hrm))
    exact (commute_zm_vv c.pu hb hx hz (hVk hu)).symm

theorem sup_zloc_inf_sup_zloc_le (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {A₁ A₂ : Subgroup (puAmalgam c.pu.le).Universal}
    (hA₁U : A₁ ≤ Uloc c.pu.le L x) (hA₂U : A₂ ≤ Uloc c.pu.le L x) (hA₁₂ : A₁ ⊓ A₂ = ⊥) :
    (A₁ ⊔ Zloc c.pu.le L x) ⊓ (A₂ ⊔ Zloc c.pu.le L x) ≤ Zloc c.pu.le L x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  set Z := Zloc c.pu.le L x with hZdef
  set U := Uloc c.pu.le L x with hUdef
  have hZc : Z ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) x : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hx
  have hUs : U ≤ stab (puAmalgam c.pu.le) x := puTrans_le_stab c.pu.le _ x
  have hZn : ∀ {A : Subgroup (puAmalgam c.pu.le).Universal}, A ≤ U →
      Z ≤ Subgroup.normalizer (A : Set _) := fun {A} hA =>
    (hZc.trans (Subgroup.centralizer_le (hA.trans hUs))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnZ : ∀ {A : Subgroup (puAmalgam c.pu.le).Universal}, A ≤ U →
      A ≤ Subgroup.normalizer (Z : Set _) := fun {A} hA =>
    (hA.trans hUs).trans ((Subgroup.le_centralizer_iff.mp hZc).trans
      (Subgroup.centralizer_le_normalizer _))
  have hUZ : Z ⊓ U = ⊥ := by rw [inf_comm]; exact uloc_inf_zloc c.pu hfull x
  have e1 : (Z ⊔ A₁) ⊓ (A₂ ⊔ Z) = Z ⊔ (A₁ ⊓ (A₂ ⊔ Z)) :=
    S45.sup_inf_eq_of_le le_sup_right (hZn hA₁U)
  have e2 : (A₂ ⊔ Z) ⊓ U = A₂ ⊔ (Z ⊓ U) := S45.sup_inf_eq_of_le hA₂U (hnZ hA₂U)
  have e3 : A₁ ⊓ (A₂ ⊔ Z) ≤ A₁ ⊓ A₂ := by
    refine le_inf inf_le_left ?_
    have : A₁ ⊓ (A₂ ⊔ Z) ≤ (A₂ ⊔ Z) ⊓ U := le_inf inf_le_right (inf_le_left.trans hA₁U)
    rw [e2, hUZ, sup_bot_eq] at this
    exact this
  rw [sup_comm A₁ Z, e1]
  exact sup_le le_rfl ((e3.trans (le_of_eq hA₁₂)).trans bot_le)

theorem mem_bzero_of_mem_vv_mul (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {x m m' : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hxm' : (puAmalgam c.pu.le).treeGraph.Adj x m')
    (hne : Usup (puAmalgam c.pu.le) x m ≠ Usup _ x m') {w w' b : (puAmalgam c.pu.le).Universal}
    (hw : w ∈ Vv (puAmalgam c.pu.le) m) (hw' : w' ∈ Vv (puAmalgam c.pu.le) m')
    (hb : b ∈ bzero c x) (hwe : w = w' * b)
    (hP : ∀ k, (puAmalgam c.pu.le).treeGraph.Adj x k →
      Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x m' ≤ Usup _ x k →
      ∀ v ∈ Vv (puAmalgam c.pu.le) k, ⁅w, v⁆ ∈ Zloc c.pu.le L x) :
    w ∈ bzero c x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  set P := Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x m' with hPdef
  have hPc : Nat.card P = 2 := by rw [card_usup_inf_usup h464 h465 c hx hxm hxm' hne, hq]
  have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPc]; norm_num)
  set Z := Zloc c.pu.le L x with hZdef
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hm' : ¬ IsMVtx (puAmalgam c.pu.le) m' := (isMVtx_iff_of_adj _ hxm').mp hx
  have hwV : w ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxm hw
  have hw'V : w' ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxm' hw'
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {v | v ∈ Vv (puAmalgam c.pu.le) x ∧ ⁅w, v⁆ ∈ Z}
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', ?_⟩
        have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ha' ((Subgroup.mem_normalizer_iff.mp
          (vv_le_normalizer_zloc c x ha) _).mp hb'')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x
          (Subgroup.inv_mem _ ha)) _).mp (Subgroup.inv_mem _ ha') }
  suffices hVS : Vv (puAmalgam c.pu.le) x ≤ S from ⟨hwV, fun v hv => (hVS hv).2⟩
  rw [vv_eq_iSup_vv hx]
  refine iSup₂_le fun k hxk => fun v hv => ⟨I466b.vv_le_vv_of_adj c.pu hx hxk hv, ?_⟩
  by_cases hPk : P ≤ Usup (puAmalgam c.pu.le) x k
  · exact hP k hxk hPk v hv
  have hk : ¬ IsMVtx (puAmalgam c.pu.le) k := (isMVtx_iff_of_adj _ hxk).mp hx
  have hvV : v ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxk hv
  have hd : ∀ {ρ}, (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      (puAmalgam c.pu.le).treeGraph.dist ρ k ≤ 2 := fun {ρ} hxρ => by
    have h1 := dist_triangle (puAmalgam c.pu.le) ρ x k
    rw [tdist_comm (puAmalgam c.pu.le) ρ x, dist_eq_one_of_adj _ hxρ,
      dist_eq_one_of_adj _ hxk] at h1
    exact h1
  have h1 : ⁅w, v⁆ ∈ (Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x k) ⊔ Z := by
    rw [← zh_inf_zh_eq h464 h465 c hx hxm hxk]
    exact commutator_vv_vv_le_zh_inf h464 c hm hk (hd hxm)
      (Subgroup.commutator_mem_commutator hw hv)
  have h2 : ⁅w, v⁆ ∈ (Usup (puAmalgam c.pu.le) x m' ⊓ Usup _ x k) ⊔ Z := by
    have e : ⁅w' * b, v⁆ = (w' * ⁅b, v⁆ * w'⁻¹) * ⁅w', v⁆ := by
      simp only [commutatorElement_def]; group
    have hbv : w' * ⁅b, v⁆ * w'⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x hw'V) _).mp (hb.2 v hvV)
    have hw'v : ⁅w', v⁆ ∈ (Usup (puAmalgam c.pu.le) x m' ⊓ Usup _ x k) ⊔ Z := by
      rw [← zh_inf_zh_eq h464 h465 c hx hxm' hxk]
      exact commutator_vv_vv_le_zh_inf h464 c hm' hk (hd hxm')
        (Subgroup.commutator_mem_commutator hw' hv)
    rw [hwe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hbv) hw'v
  have hPk' : P ⊓ Usup (puAmalgam c.pu.le) x k = ⊥ := by
    have hdvd : Nat.card ↥(P ⊓ Usup (puAmalgam c.pu.le) x k) ∣ 2 :=
      hPc ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne2 : Nat.card ↥(P ⊓ Usup (puAmalgam c.pu.le) x k) ≠ 2 := fun h => hPk (by
      have : P ⊓ Usup (puAmalgam c.pu.le) x k = P :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hPc])
      rw [← this]; exact inf_le_right)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exact absurd h hne2
  have hA₁₂ : (Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x k) ⊓ (Usup _ x m' ⊓ Usup _ x k) = ⊥ :=
    le_bot_iff.mp (le_trans (le_inf (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right)) hPk'.le)
  exact sup_zloc_inf_sup_zloc_le c hx (inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxm))
    (inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxm')) hA₁₂ ⟨h1, h2⟩

theorem commutator_vv_ptQ_le_bzero_of (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {x ℓ m : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x m) {y : (puAmalgam c.pu.le).Universal}
    (hyℓ : y ∈ Qv (puAmalgam c.pu.le) ℓ)
    (hyP : y ∈ ptQ (puAmalgam c.pu.le) x (Usup _ x ℓ ⊓ Usup _ x m))
    (hyx : y ∉ Qv (puAmalgam c.pu.le) x)
    (h : ∀ v ∈ Vv (puAmalgam c.pu.le) m, ⁅v, y⁆ ∈ bzero c x) :
    ⁅Vv (puAmalgam c.pu.le) m, ptQ _ x (Usup _ x ℓ ⊓ Usup _ x m)⁆ ≤ bzero c x := by
  have h464' := h464 G M T L F φ c
  set P := Usup (puAmalgam c.pu.le) x ℓ ⊓ Usup _ x m with hPdef
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hPℓ : IsPtOn (puAmalgam c.pu.le) x ℓ P := ⟨m, hxm, Ne.symm hne, rfl⟩
  have hroot : (Qv (puAmalgam c.pu.le) x).relIndex (Qv _ ℓ ⊓ ptQ _ x P) = 2 := by
    rw [relIndex_qv_inf_ptQ h464 h465 h466a c hx hxℓ hPℓ, hq]
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x :=
    inf_le_left.trans ((h464' x ℓ hx hxℓ).trans (zh_le_zm _ hxℓ))
  have hQx : Qv (puAmalgam c.pu.le) x ≤ Qv _ ℓ ⊓ ptQ _ x P :=
    le_inf (qv_le_qv _ c.pu.hyp20 hx hxℓ) (qv_le_ptQ c hx hPZ)
  have hKB : ptQ (puAmalgam c.pu.le) x P ≤ Subgroup.normalizer (bzero c x : Set _) :=
    fun r hr => stab_le_normalizer_bzero c x (mem_ptQ.mp hr).1
  have hVQ : ∀ r ∈ Qv (puAmalgam c.pu.le) x, ∀ v ∈ Vv (puAmalgam c.pu.le) m,
      ⁅v, r⁆ ∈ bzero c x := fun r hr v hv =>
    zm_le_bzero c hx ((h465 G M T L F φ c x ℓ hx hxℓ).2.2
      (Subgroup.commutator_mem_commutator (I466b.vv_le_vv_of_adj c.pu hx hxm hv) hr))
  have h1 : ∀ r ∈ Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P, ∀ v ∈ Vv (puAmalgam c.pu.le) m,
      ⁅v, r⁆ ∈ bzero c x := by
    refine commutator_mem_of_le_closure (fun r hr => hKB hr.2)
      (le_closure_of_relIndex_eq_two hQx hroot ⟨hyℓ, hyP⟩ hyx) ?_ ?_
    · rintro r (hr | hr)
      · exact hQx hr
      · rw [Set.mem_singleton_iff.mp hr]; exact ⟨hyℓ, hyP⟩
    · rintro r (hr | hr)
      · exact hVQ r hr
      · rw [Set.mem_singleton_iff.mp hr]; exact h
  have h2 : ∀ r ∈ ptQ (puAmalgam c.pu.le) x P, ∀ v ∈ Vv (puAmalgam c.pu.le) m,
      ⁅v, r⁆ ∈ bzero c x := by
    refine commutator_mem_of_le_closure hKB ?_ ?_ ?_
      (s := ((Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P : Subgroup _) : Set _) ∪
        ((Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P : Subgroup _) : Set _))
    · rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      exact ptQ_le_sup_qv_inf h464 h465 h466a c hx hxℓ hxm hne rfl
    · rintro r (hr | hr)
      · exact hr.2
      · exact hr.2
    · rintro r (hr | hr) v hv
      · exact h1 r hr v hv
      · exact zm_le_bzero c hx (zh_le_zm _ hxm (commutator_vv_qv_le_zh c.pu h464' hm
          (Subgroup.commutator_mem_commutator hv hr.1)))
  exact Subgroup.commutator_le.mpr fun v hv r hr => h2 r hr v hv

theorem commutator_vv_ptQ_le_centralizer_pencil (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) (hq : Fintype.card F = 2) {x m : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPm : P ≤ Usup (puAmalgam c.pu.le) x m)
    (hPc : Nat.card P = 2) :
    ⁅Vv (puAmalgam c.pu.le) m, ptQ _ x P⁆ ≤
      Subgroup.centralizer (pencil (puAmalgam c.pu.le) x P : Set _) := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPc]; norm_num)
  refine Subgroup.commutator_le.mpr fun v hv r hr => Subgroup.mem_centralizer_iff.mpr ?_
  have hle : pencil (puAmalgam c.pu.le) x P ≤ Subgroup.centralizer ({⁅v, r⁆} : Set _) := by
    refine pencil_le fun k hxk hPk => fun u hu => Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    rw [Set.mem_singleton_iff.mp hg]
    by_cases he : Usup (puAmalgam c.pu.le) x k = Usup _ x m
    · rw [vv_eq_of_usup_eq h464 h465 h466a c hx hxk hxm he] at hu
      have hvr : ⁅v, r⁆ ∈ Vv (puAmalgam c.pu.le) m := by
        have hr' := (Subgroup.mem_normalizer_iff.mp
          (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm hPm hr) v).mp hv
        have e : ⁅v, r⁆ = v * (r * v * r⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ hv (Subgroup.inv_mem _ hr')
      exact vv_comm c.pu hb hm hvr hu
    · have hc := card_usup_inf_usup h464 h465 c hx hxk hxm he
      have : Finite ↥(Usup (puAmalgam c.pu.le) x k ⊓ Usup _ x m) :=
        Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
      have hPe : P = Usup (puAmalgam c.pu.le) x k ⊓ Usup _ x m :=
        Subgroup.eq_of_le_of_card_ge (le_inf hPk hPm) (by rw [hc, hPc, hq])
      rw [hPe] at hr
      exact (commute_vv_commutator_vv_ptQ h464 h465 h466a c hq hx hxk hxm he hu hv hr).symm
  exact fun y hy => (Subgroup.mem_centralizer_iff.mp (hle hy) ⁅v, r⁆ rfl).symm

end Amalgam

end CFSG.Quasithin.MS93.S46R
