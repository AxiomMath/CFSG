module

public import CFSG.Quasithin.Recognition.J2RecCzNorm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM

@[expose] def J2Cz.pc : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem J2Cz.pc_mem : pc ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem J2Cz.pc_sq : pc * pc = 1 := by decide

theorem J2Cz.pa_pc_comm : pa * pc = pc * pa := by decide

theorem J2Cz.pa_pc_sq : pa * pc * (pa * pc) = 1 := by decide

theorem J2Cz.pc_ne_one : pc ≠ 1 := by decide

theorem J2Cz.pa_pc_ne_one : pa * pc ≠ 1 := by decide

theorem J2Cz.pa_four : pa 4 = 4 := by decide

theorem J2Cz.pc_four : pc 4 = 4 := by decide

theorem J2Cz.eq_of_comm_pa : ∀ σ : Perm (Fin 5), σ * pa = pa * σ → Perm.sign σ = 1 →
    σ = 1 ∨ σ = pa ∨ σ = pc ∨ σ = pa * pc := by
  decide +kernel

theorem J2Cz.QM.eq_of_phiAHom_eq : ∀ p : QM, phiAHom p = p →
    p = 1 ∨ p = z ∨ p = x 4 ∨ p = z * x 4 := by
  decide +kernel

theorem J2Cz.QM.mul_self_of_fix : ∀ p : QM, (p = 1 ∨ p = z ∨ p = x 4 ∨ p = z * x 4) →
    p * p = 1 := by
  decide +kernel

theorem J2Cz.QM.comm_of_fix : ∀ p q : QM, (p = 1 ∨ p = z ∨ p = x 4 ∨ p = z * x 4) →
    (q = 1 ∨ q = z ∨ q = x 4 ∨ q = z * x 4) → p * q = q * p := by
  decide +kernel

structure J2Frame (G : Type) [Group G] (z : G) : Type where
  isTypeH2 : IsTypeH2 G z
  L : Subgroup G
  le : L ≤ Subgroup.centralizer ({z} : Set G)
  inf_eq_bot : L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥
  card_eq : Nat.card L = 60
  χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM
  χ_z : ((χ.symm J2Cz.QM.z : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = z
  act_mem : ∀ l (hl : l ∈ L), IsTypeH2.czAct χ ⟨l, le hl⟩ ∈ L0

namespace J2Frame

variable {G : Type} [Group G] {z : G}

theorem exists_frame [Finite G] (h : IsTypeH2 G z) {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLQ : L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥) (hL : Nat.card L = 60) :
    ∃ F : J2Frame G z, F.L = L := by
  obtain ⟨χ, hχz, hχL⟩ := h.exists_equiv_QM_complement hLC hLQ hL
  exact ⟨⟨h, L, hLC, hLQ, hL, χ, hχz, hχL⟩, rfl⟩

variable (F : J2Frame G z)

@[expose] noncomputable def lineHomL : ↥F.L →* alternatingGroup (Fin 5) where
  toFun l := ⟨linePerm (IsTypeH2.czAct F.χ ⟨l, F.le l.2⟩),
    linePerm_mem_alternatingGroup (F.act_mem l l.2)⟩
  map_one' := Subtype.ext (by
    show linePermHom (IsTypeH2.czAct F.χ 1) = 1
    rw [map_one, map_one])
  map_mul' l l' := Subtype.ext (by
    show linePermHom (IsTypeH2.czAct F.χ (⟨l, F.le l.2⟩ * ⟨l', F.le l'.2⟩)) =
      linePermHom (IsTypeH2.czAct F.χ ⟨l, F.le l.2⟩) *
        linePermHom (IsTypeH2.czAct F.χ ⟨l', F.le l'.2⟩)
    rw [map_mul, map_mul])

theorem eq_of_linePerm_eq {α β : MulAut QM} (hα : α ∈ L0) (hβ : β ∈ L0)
    (h : linePerm α = linePerm β) : α = β :=
  aut_ext fun j => by rw [mem_L0.mp hα, mem_L0.mp hβ, h]

theorem lineHomL_bijective : Function.Bijective F.lineHomL := by
  refine ⟨fun l l' hll' => ?_, fun σ => ?_⟩
  · have h1 : linePerm (IsTypeH2.czAct F.χ ⟨l, F.le l.2⟩) =
        linePerm (IsTypeH2.czAct F.χ ⟨l', F.le l'.2⟩) := congrArg Subtype.val hll'
    exact Subtype.ext (F.isTypeH2.czAct_injOn F.χ F.le F.inf_eq_bot l.2 l'.2
      (eq_of_linePerm_eq (F.act_mem _ l.2) (F.act_mem _ l'.2) h1))
  · obtain ⟨l, hl, hlα⟩ := F.isTypeH2.exists_mem_czAct_eq F.χ F.le F.inf_eq_bot F.card_eq
      F.act_mem (lineEquiv.symm σ).2
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    show linePerm (IsTypeH2.czAct F.χ ⟨l, F.le hl⟩) = σ
    rw [hlα, linePerm_lineEquiv_symm]

@[expose] noncomputable def lineEquivL : ↥F.L ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective F.lineHomL F.lineHomL_bijective

@[expose] noncomputable def ι : alternatingGroup (Fin 5) →* G :=
  F.L.subtype.comp F.lineEquivL.symm.toMonoidHom

theorem ι_mem (σ : alternatingGroup (Fin 5)) : F.ι σ ∈ F.L := (F.lineEquivL.symm σ).2

theorem ι_mem_centralizer (σ : alternatingGroup (Fin 5)) :
    F.ι σ ∈ Subgroup.centralizer ({z} : Set G) :=
  F.le (F.ι_mem σ)

theorem ι_comm_z (σ : alternatingGroup (Fin 5)) : F.ι σ * z = z * F.ι σ :=
  Subgroup.mem_centralizer_singleton_iff.mp (F.ι_mem_centralizer σ)

theorem ι_injective : Function.Injective F.ι :=
  Subtype.val_injective.comp F.lineEquivL.symm.injective

theorem exists_ι_eq {l : G} (hl : l ∈ F.L) : ∃ σ, F.ι σ = l := by
  refine ⟨F.lineEquivL ⟨l, hl⟩, ?_⟩
  show ((F.lineEquivL.symm (F.lineEquivL ⟨l, hl⟩) : ↥F.L) : G) = l
  rw [MulEquiv.symm_apply_apply]

theorem czAct_ι (σ : alternatingGroup (Fin 5))
    (hσ : F.ι σ ∈ Subgroup.centralizer ({z} : Set G)) :
    IsTypeH2.czAct F.χ ⟨F.ι σ, hσ⟩ = (lineEquiv.symm σ : MulAut QM) := by
  have h1 : F.lineHomL (F.lineEquivL.symm σ) = σ := F.lineEquivL.apply_symm_apply σ
  have h2 : linePerm (IsTypeH2.czAct F.χ ⟨F.ι σ, hσ⟩) = σ := congrArg Subtype.val h1
  exact eq_of_linePerm_eq (F.act_mem _ (F.ι_mem σ)) (lineEquiv.symm σ).2
    (h2.trans (linePerm_lineEquiv_symm σ).symm)

theorem czAct_ι_x (σ : alternatingGroup (Fin 5))
    (hσ : F.ι σ ∈ Subgroup.centralizer ({z} : Set G)) (j : Fin 5) :
    IsTypeH2.czAct F.χ ⟨F.ι σ, hσ⟩ (x j) = x ((σ : Perm (Fin 5)) j) := by
  rw [F.czAct_ι σ hσ, mem_L0.mp (lineEquiv.symm σ).2 j, linePerm_lineEquiv_symm]

theorem linePerm_czAct_ι (σ : alternatingGroup (Fin 5))
    (hσ : F.ι σ ∈ Subgroup.centralizer ({z} : Set G)) :
    linePerm (IsTypeH2.czAct F.χ ⟨F.ι σ, hσ⟩) = σ := by
  rw [F.czAct_ι σ hσ, linePerm_lineEquiv_symm]

@[expose] noncomputable def emb : QM →* G :=
  (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))).subtype.comp F.χ.symm.toMonoidHom

theorem emb_injective : Function.Injective F.emb :=
  Subtype.val_injective.comp F.χ.symm.injective

theorem emb_mem (p : QM) : F.emb p ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
  (F.χ.symm p).2

theorem emb_z : F.emb J2Cz.QM.z = z := F.χ_z

theorem emb_χ {q : G} (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    F.emb (F.χ ⟨q, hq⟩) = q := by
  show ((F.χ.symm (F.χ ⟨q, hq⟩) : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) = q
  rw [MulEquiv.symm_apply_apply]

theorem exists_emb_eq {q : G} (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ p, F.emb p = q :=
  ⟨_, F.emb_χ hq⟩

theorem conj_emb (g : ↥(Subgroup.centralizer ({z} : Set G))) (p : QM) :
    (g : G) * F.emb p * (g : G)⁻¹ = F.emb (IsTypeH2.czAct F.χ g p) :=
  (IsTypeH2.czAct_apply F.χ g p).symm

@[expose] noncomputable def pt (j : Fin 5) : G := F.emb (x j)

theorem pt_mem (j : Fin 5) : F.pt j ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
  F.emb_mem _

theorem ι_conj_pt (σ : alternatingGroup (Fin 5)) (j : Fin 5) :
    F.ι σ * F.pt j * (F.ι σ)⁻¹ = F.pt ((σ : Perm (Fin 5)) j) := by
  have h1 := F.conj_emb ⟨F.ι σ, F.ι_mem_centralizer σ⟩ (x j)
  rw [F.czAct_ι_x] at h1
  exact h1

@[expose] noncomputable def t : G := F.ι ⟨pa, pa_mem⟩

@[expose] noncomputable def a : G := F.ι ⟨pc, pc_mem⟩

theorem t_eq : F.t = F.ι ⟨pa, pa_mem⟩ := rfl

theorem a_eq : F.a = F.ι ⟨pc, pc_mem⟩ := rfl

theorem t_mem_L : F.t ∈ F.L := F.ι_mem _

theorem a_mem_L : F.a ∈ F.L := F.ι_mem _

theorem t_mem_centralizer : F.t ∈ Subgroup.centralizer ({z} : Set G) := F.ι_mem_centralizer _

theorem a_mem_centralizer : F.a ∈ Subgroup.centralizer ({z} : Set G) := F.ι_mem_centralizer _

theorem czAct_t (ht : F.t ∈ Subgroup.centralizer ({z} : Set G)) :
    IsTypeH2.czAct F.χ ⟨F.t, ht⟩ = phiA :=
  (F.czAct_ι _ ht).trans lineEquiv_symm_pa

theorem ι_mul_comm {σ τ : alternatingGroup (Fin 5)} (h : (σ : Perm (Fin 5)) * τ = τ * σ) :
    F.ι σ * F.ι τ = F.ι τ * F.ι σ := by
  rw [← map_mul, ← map_mul, show σ * τ = τ * σ from Subtype.ext h]

theorem ι_mul_self {σ : alternatingGroup (Fin 5)} (h : (σ : Perm (Fin 5)) * σ = 1) :
    F.ι σ * F.ι σ = 1 := by
  rw [← map_mul, show σ * σ = 1 from Subtype.ext h, map_one]

theorem t_mul_t : F.t * F.t = 1 := F.ι_mul_self pa_sq

theorem a_mul_a : F.a * F.a = 1 := F.ι_mul_self pc_sq

theorem t_mul_a_comm : F.t * F.a = F.a * F.t := F.ι_mul_comm pa_pc_comm

theorem ta_mul_ta : F.t * F.a * (F.t * F.a) = 1 := by
  rw [t_eq, a_eq, ← map_mul]
  exact F.ι_mul_self (σ := ⟨pa, pa_mem⟩ * ⟨pc, pc_mem⟩) pa_pc_sq

theorem t_ne_one : F.t ≠ 1 := fun h1 =>
  pa_ne_one (congrArg Subtype.val (F.ι_injective (h1.trans (map_one F.ι).symm)))

theorem a_ne_one : F.a ≠ 1 := fun h1 =>
  pc_ne_one (congrArg Subtype.val (F.ι_injective (h1.trans (map_one F.ι).symm)))

theorem ta_ne_one : F.t * F.a ≠ 1 := fun h1 => by
  rw [t_eq, a_eq, ← map_mul] at h1
  exact pa_pc_ne_one (congrArg Subtype.val (F.ι_injective (h1.trans (map_one F.ι).symm)))

theorem eq_one_of_mem_L_of_mem_Q {l : G} (hl : l ∈ F.L)
    (hlQ : l ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) : l = 1 := by
  have h1 : l ∈ F.L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := ⟨hl, hlQ⟩
  rwa [F.inf_eq_bot, Subgroup.mem_bot] at h1

@[expose] noncomputable def X : Subgroup G := Subgroup.centralizer ({F.t} : Set G)

@[expose] noncomputable def T : Subgroup G := F.X ⊓ Subgroup.centralizer ({z} : Set G)

@[expose] noncomputable def W : Subgroup G := F.X ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))

theorem mem_X {g : G} : g ∈ F.X ↔ g * F.t = F.t * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem T_le_X : F.T ≤ F.X := inf_le_left

theorem T_le_centralizer : F.T ≤ Subgroup.centralizer ({z} : Set G) := inf_le_right

theorem W_le_T : F.W ≤ F.T := inf_le_inf_left _ (pCoreOf_le 2 _)

theorem t_mem_X : F.t ∈ F.X := F.mem_X.mpr rfl

theorem t_mem_T : F.t ∈ F.T := ⟨F.t_mem_X, F.t_mem_centralizer⟩

theorem a_mem_X : F.a ∈ F.X := F.mem_X.mpr F.t_mul_a_comm.symm

theorem a_mem_T : F.a ∈ F.T := ⟨F.a_mem_X, F.a_mem_centralizer⟩

theorem z_mem_X : z ∈ F.X :=
  F.mem_X.mpr (Subgroup.mem_centralizer_singleton_iff.mp F.t_mem_centralizer).symm

theorem z_mem_W : z ∈ F.W := ⟨F.z_mem_X, F.isTypeH2.z_mem_pCoreOf⟩

theorem pt_four_mem_W : F.pt 4 ∈ F.W := by
  refine ⟨F.mem_X.mpr ?_, F.pt_mem 4⟩
  have h1 := F.ι_conj_pt ⟨pa, pa_mem⟩ 4
  rw [show ((⟨pa, pa_mem⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) 4 = 4 from pa_four,
    ← t_eq] at h1
  calc F.pt 4 * F.t = F.t * F.pt 4 * F.t⁻¹ * F.t := by rw [h1]
    _ = F.t * F.pt 4 := by group

theorem mem_W {w : G} : w ∈ F.W ↔ w = 1 ∨ w = z ∨ w = F.pt 4 ∨ w = z * F.pt 4 := by
  constructor
  · rintro ⟨hwX, hwQ⟩
    obtain ⟨p, rfl⟩ := F.exists_emb_eq hwQ
    have h1 : F.emb (phiAHom p) = F.emb p := by
      have h2 := F.conj_emb ⟨F.t, F.t_mem_centralizer⟩ p
      rw [F.czAct_t] at h2
      rw [show phiAHom p = phiA p from rfl, ← h2]
      calc F.t * F.emb p * F.t⁻¹ = F.emb p * F.t * F.t⁻¹ := by rw [F.mem_X.mp hwX]
        _ = F.emb p := by group
    rcases eq_of_phiAHom_eq p (F.emb_injective h1) with rfl | rfl | rfl | rfl
    · left; exact map_one _
    · right; left; exact F.emb_z
    · right; right; left; rfl
    · right; right; right; rw [map_mul, F.emb_z]; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact F.z_mem_W
    · exact F.pt_four_mem_W
    · exact F.W.mul_mem F.z_mem_W F.pt_four_mem_W

theorem exists_emb_of_mem_W {w : G} (hw : w ∈ F.W) :
    ∃ p : QM, (p = 1 ∨ p = J2Cz.QM.z ∨ p = x 4 ∨ p = J2Cz.QM.z * x 4) ∧ F.emb p = w := by
  rcases F.mem_W.mp hw with rfl | rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, map_one _⟩
  · exact ⟨J2Cz.QM.z, Or.inr (Or.inl rfl), F.emb_z⟩
  · exact ⟨x 4, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨J2Cz.QM.z * x 4, Or.inr (Or.inr (Or.inr rfl)), by rw [map_mul, F.emb_z]; rfl⟩

theorem mul_self_of_mem_W {w : G} (hw : w ∈ F.W) : w * w = 1 := by
  obtain ⟨p, hp, rfl⟩ := F.exists_emb_of_mem_W hw
  rw [← map_mul, mul_self_of_fix p hp, map_one]

theorem comm_of_mem_W {w w' : G} (hw : w ∈ F.W) (hw' : w' ∈ F.W) : w * w' = w' * w := by
  obtain ⟨p, hp, rfl⟩ := F.exists_emb_of_mem_W hw
  obtain ⟨q, hq, rfl⟩ := F.exists_emb_of_mem_W hw'
  rw [← map_mul, ← map_mul, comm_of_fix p q hp hq]

theorem eq_of_mem_L_of_mem_X {l : G} (hl : l ∈ F.L) (hlX : l ∈ F.X) :
    l = 1 ∨ l = F.t ∨ l = F.a ∨ l = F.t * F.a := by
  obtain ⟨σ, rfl⟩ := F.exists_ι_eq hl
  have h1 : σ * ⟨pa, pa_mem⟩ = ⟨pa, pa_mem⟩ * σ :=
    F.ι_injective (by rw [map_mul, map_mul]; exact F.mem_X.mp hlX)
  rcases eq_of_comm_pa σ (congrArg Subtype.val h1) (Perm.mem_alternatingGroup.mp σ.2) with
    h2 | h2 | h2 | h2
  · left
    rw [show σ = 1 from Subtype.ext h2, map_one]
  · right; left
    rw [show σ = ⟨pa, pa_mem⟩ from Subtype.ext h2]
    rfl
  · right; right; left
    rw [show σ = ⟨pc, pc_mem⟩ from Subtype.ext h2]
    rfl
  · right; right; right
    rw [show σ = ⟨pa, pa_mem⟩ * ⟨pc, pc_mem⟩ from Subtype.ext h2, map_mul]
    rfl

theorem exists_mem_L_mul_eq {g : G} (hg : g ∈ F.T) :
    ∃ l ∈ F.L, l ∈ F.X ∧ ∃ w ∈ F.W, g = l * w := by
  obtain ⟨hgX, hgH⟩ := hg
  set gH : ↥(Subgroup.centralizer ({z} : Set G)) := ⟨g, hgH⟩ with hgH'
  set σ : alternatingGroup (Fin 5) :=
    ⟨linePerm (IsTypeH2.czAct F.χ gH), F.isTypeH2.linePerm_czAct_mem F.χ gH⟩ with hσ
  have hσpa : σ * ⟨pa, pa_mem⟩ = ⟨pa, pa_mem⟩ * σ := by
    apply Subtype.ext
    have h1 : gH * ⟨F.t, F.t_mem_centralizer⟩ = ⟨F.t, F.t_mem_centralizer⟩ * gH :=
      Subtype.ext (F.mem_X.mp hgX)
    have h2 := congrArg (fun k => linePermHom (IsTypeH2.czAct F.χ k)) h1
    simp only [map_mul, linePermHom_apply, F.czAct_t, linePerm_phiA] at h2
    exact h2
  have hlX : F.ι σ ∈ F.X := by
    rw [F.mem_X, t_eq, ← map_mul, ← map_mul, hσpa]
  refine ⟨F.ι σ, F.ι_mem σ, hlX, (F.ι σ)⁻¹ * g, ⟨F.X.mul_mem (F.X.inv_mem hlX) hgX, ?_⟩,
    by group⟩
  have h3 : linePerm (IsTypeH2.czAct F.χ (⟨F.ι σ, F.ι_mem_centralizer σ⟩⁻¹ * gH)) = 1 := by
    rw [← linePermHom_apply, map_mul, map_mul, map_inv, map_inv, linePermHom_apply,
      linePermHom_apply, F.linePerm_czAct_ι]
    exact inv_mul_cancel _
  exact F.isTypeH2.mem_pCoreOf_of_linePerm_eq_one F.χ h3

theorem comm_and_mul_self_of_mem_L_of_mem_X {l : G} (hl : l ∈ F.L) (hlX : l ∈ F.X) :
    l * l = 1 ∧ ∀ w ∈ F.W, l * w = w * l := by
  have hz : l * z = z * l := Subgroup.mem_centralizer_singleton_iff.mp (F.le hl)
  have h4 : ∀ σ : alternatingGroup (Fin 5), (σ : Perm (Fin 5)) 4 = 4 →
      F.ι σ * F.pt 4 = F.pt 4 * F.ι σ := fun σ hσ4 => by
    have h1 := F.ι_conj_pt σ 4
    rw [hσ4] at h1
    calc F.ι σ * F.pt 4 = F.ι σ * F.pt 4 * (F.ι σ)⁻¹ * F.ι σ := by group
      _ = F.pt 4 * F.ι σ := by rw [h1]
  have hx : l * F.pt 4 = F.pt 4 * l := by
    rcases F.eq_of_mem_L_of_mem_X hl hlX with rfl | rfl | rfl | rfl
    · group
    · exact h4 _ pa_four
    · exact h4 _ pc_four
    · rw [t_eq, a_eq, ← map_mul]
      exact h4 _ (by show pa (pc 4) = 4; rw [pc_four, pa_four])
  refine ⟨?_, fun w hw => ?_⟩
  · rcases F.eq_of_mem_L_of_mem_X hl hlX with rfl | rfl | rfl | rfl
    · group
    · exact F.t_mul_t
    · exact F.a_mul_a
    · exact F.ta_mul_ta
  · rcases F.mem_W.mp hw with rfl | rfl | rfl | rfl
    · group
    · exact hz
    · exact hx
    · calc l * (z * F.pt 4) = (l * z) * F.pt 4 := by group
        _ = z * (l * F.pt 4) := by rw [hz]; group
        _ = z * F.pt 4 * l := by rw [hx]; group

theorem exists_eq_mul_of_mem_T {g : G} (hg : g ∈ F.T) :
    ∃ l, (l = 1 ∨ l = F.t ∨ l = F.a ∨ l = F.t * F.a) ∧ ∃ w ∈ F.W, g = l * w := by
  obtain ⟨l, hl, hlX, w, hw, rfl⟩ := F.exists_mem_L_mul_eq hg
  exact ⟨l, F.eq_of_mem_L_of_mem_X hl hlX, w, hw, rfl⟩

theorem mul_self_of_mem_T {g : G} (hg : g ∈ F.T) : g * g = 1 := by
  obtain ⟨l, hl, hlX, w, hw, rfl⟩ := F.exists_mem_L_mul_eq hg
  obtain ⟨hll, hlw⟩ := F.comm_and_mul_self_of_mem_L_of_mem_X hl hlX
  calc l * w * (l * w) = l * (w * l) * w := by group
    _ = l * l * (w * w) := by rw [← hlw w hw]; group
    _ = 1 := by rw [hll, F.mul_self_of_mem_W hw, one_mul]

theorem comm_of_mem_T {g g' : G} (hg : g ∈ F.T) (hg' : g' ∈ F.T) : g * g' = g' * g := by
  have h1 := F.mul_self_of_mem_T (F.T.mul_mem hg hg')
  have h2 := F.mul_self_of_mem_T hg
  have h3 := F.mul_self_of_mem_T hg'
  calc g * g' = g * g' * (g' * g * (g' * g)) := by rw [F.mul_self_of_mem_T (F.T.mul_mem hg' hg),
        mul_one]
    _ = g * (g' * g') * g * (g' * g) := by group
    _ = g * g * (g' * g) := by rw [h3, mul_one]
    _ = g' * g := by rw [h2, one_mul]

theorem t_not_mem_Q : F.t ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := fun h1 =>
  F.t_ne_one (F.eq_one_of_mem_L_of_mem_Q F.t_mem_L h1)

theorem t_not_mem_W : F.t ∉ F.W := fun h1 => F.t_not_mem_Q h1.2

theorem a_not_mem_W : F.a ∉ F.W := fun h1 =>
  F.a_ne_one (F.eq_one_of_mem_L_of_mem_Q F.a_mem_L h1.2)

theorem ta_not_mem_W : F.t * F.a ∉ F.W := fun h1 =>
  F.ta_ne_one (F.eq_one_of_mem_L_of_mem_Q (F.L.mul_mem F.t_mem_L F.a_mem_L) h1.2)

end J2Frame

end CFSG.Quasithin
