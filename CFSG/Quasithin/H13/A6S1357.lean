module

public import CFSG.Quasithin.H13.A6S1356

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def R8 : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
    swap 0 3 * swap 1 2 * swap 4 5]

@[expose] def FixW3Mod (σ : Perm (Fin 6)) : Prop :=
  ∀ x : P6, InW34 x → act4f σ x * x⁻¹ = 1 ∨ act4f σ x * x⁻¹ = e0123

instance (σ : Perm (Fin 6)) : Decidable (FixW3Mod σ) := by unfold FixW3Mod; infer_instance

theorem mem_R8 : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → FixW3Mod σ → σ ∈ R8 := by
  decide +kernel

@[expose] def Quad (σ τ : Perm (Fin 6)) : Prop :=
  ∀ x : P6, InW4 x → act4f τ (act4f σ x * x⁻¹) = act4f σ x * x⁻¹

instance (σ τ : Perm (Fin 6)) : Decidable (Quad σ τ) := by unfold Quad; infer_instance

theorem quad_R8 : ∀ σ ∈ R8, ∀ τ ∈ R8, σ ≠ 1 → τ ≠ 1 → σ ≠ τ → Quad σ τ →
    σ = swap 4 5 ∨ τ = swap 4 5 ∨ σ * τ = swap 4 5 := by
  decide +kernel

@[expose] def C3 : List (Perm (Fin 6)) :=
  [1, swap 1 2 * swap 2 3, swap 1 2 * swap 2 3 * (swap 1 2 * swap 2 3)]

@[expose] def SynWit (σ π : Perm (Fin 6)) : Prop :=
  ∀ y : P6, InW2 y → ∃ x : P6, InW4 x ∧ act4f π y = x * (act4f σ x)⁻¹

instance (σ π : Perm (Fin 6)) : Decidable (SynWit σ π) := by unfold SynWit; infer_instance

theorem synWit : ∀ σ ∈ R8, σ ≠ 1 → σ ≠ swap 4 5 → ∃ π ∈ C3, SynWit σ π := by
  decide +kernel

theorem C3_sign : ∀ π ∈ C3, Perm.sign π = 1 := by
  decide +kernel

theorem card_fix_R8 : ∀ σ ∈ R8, σ ≠ 1 → σ ≠ swap 4 5 →
    Fintype.card {x : P6 // InW4 x ∧ act4f σ x = x} = 4 := by
  decide +kernel

@[expose] def FixW3 (σ : Perm (Fin 6)) : Prop := ∀ x : P6, InW34 x → act4f σ x = x

instance (σ : Perm (Fin 6)) : Decidable (FixW3 σ) := by unfold FixW3; infer_instance

theorem fixW3_iff : ∀ σ : Perm (Fin 6), FixW3 σ → σ = 1 ∨ σ = swap 4 5 := by
  decide +kernel

theorem t_facts : FixW3 (swap 4 5) ∧ Perm.sign (swap (4 : Fin 6) 5) = -1 ∧
    swap (4 : Fin 6) 5 ≠ 1 ∧ (swap (4 : Fin 6) 5) ^ 2 = 1 := by
  decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V1_lt_V3 : fsuV1 T V < S.V3 := by
  refine lt_of_le_of_ne (S.V1_le_V2.trans S.V2_le_V3) fun h => ?_
  have := S.card_V3
  rw [← h, S.card_V1] at this
  omega

theorem G1_le_centralizer_V1 : S.G1 ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases S.mem_V1_iff.1 hv with rfl | rfl
  · simp
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

theorem G1_le_normalizer_V1 : S.G1 ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
  rw [S.normalizer_V1]
  exact le_rfl

theorem charTwo_of_inH {H : Subgroup G} (hH : InH T H) : CharTwo H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  subst hP
  exact CFSG.Quasithin.charTwo_of_inH S.h13.qtke.2.1 P hH

theorem rho_eq_of_conjAct_eq {x y : ↥(Subgroup.normalizer (V : Set G))}
    (h : conjAct V x = conjAct V y) : S.frame.ρ x = S.frame.ρ y := by
  apply act4_injective
  refine MulEquiv.ext fun w => ?_
  obtain ⟨v, rfl⟩ := S.frame.ψ.surjective w
  rw [← S.frame.equiv, ← S.frame.equiv, h]

theorem symm_mem_V3 {x : ↥W4} (hx : InW3 (x : P6)) : ((S.frame.ψ.symm x : ↥V) : G) ∈ S.V3 := by
  have e : S.frame.ψ ⟨((S.frame.ψ.symm x : ↥V) : G), (S.frame.ψ.symm x).2⟩ = x :=
    S.frame.ψ.apply_symm_apply x
  exact S.mem_pre.2 ⟨(S.frame.ψ.symm x).2, by rw [e]; exact hx⟩

theorem fixW3_of_centralizer {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : (x : G) ∈ Subgroup.centralizer (S.V3 : Set G)) : FixW3 (S.frame.ρ x) := by
  intro w hw
  have hv3 := S.symm_mem_V3 (x := ⟨w, hw.1⟩) hw.2
  have := (S.conj_eq_iff x (S.frame.ψ.symm ⟨w, hw.1⟩)).1 (by
    have := Subgroup.mem_centralizer_iff.mp hx _ hv3
    calc (x : G) * (S.frame.ψ.symm ⟨w, hw.1⟩ : G) * (x : G)⁻¹ =
        (S.frame.ψ.symm ⟨w, hw.1⟩ : G) * x * (x : G)⁻¹ := by rw [this]
      _ = _ := by group)
  rw [MulEquiv.apply_symm_apply] at this
  exact congrArg Subtype.val this

theorem centralizer_of_fixW3 {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : FixW3 (S.frame.ρ x)) : (x : G) ∈ Subgroup.centralizer (S.V3 : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨hvV, hv3⟩ := S.mem_pre.1 hv
  have h : act4 (S.frame.ρ x) (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ :=
    Subtype.ext (hx _ ⟨(S.frame.ψ ⟨v, hvV⟩).2, hv3⟩)
  have := (S.conj_eq_iff x ⟨v, hvV⟩).2 h
  calc v * x = x * v * (x : G)⁻¹ * x := by rw [this]
    _ = x * v := by group

theorem mem_centralizer_V_of_odd (h13315 : Stmt13_3_15) {y : G}
    (hy : y ∈ Subgroup.centralizer (S.V3 : Set G)) (hodd : ∃ m : ℕ, Odd m ∧ y ^ m = 1) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  have hyN := S.centralizer_V3_le h13315 hy
  refine (S.rho_eq_one_iff ⟨y, hyN⟩).1 ?_
  rcases fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨y, hyN⟩) hy) with h | h
  · exact h
  · exfalso
    obtain ⟨m, ⟨k, rfl⟩, hm⟩ := hodd
    have h1 : S.frame.ρ (⟨y, hyN⟩ ^ (2 * k + 1)) = 1 := by
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ (2 * k + 1) = 1 :=
        Subtype.ext (by simpa using hm)
      rw [this, map_one]
    rw [map_pow, h, pow_succ, pow_mul, t_facts.2.2.2, one_pow, one_mul] at h1
    exact t_facts.2.2.1 h1

theorem coreIn_le_pCoreOf
    (h13315 : Stmt13_3_15) {H : Subgroup G} (hH : H ∈ S.Hz) :
    coreIn (centralizerMod (fsuV1 T V) H S.V3) H ≤ pCoreOf 2 H :=
  coreIn_le_pCoreOf_of S.uniqueM (le_sup_right.trans hH.1.1) hH.2.2
    (S.charTwo_of_inH ⟨le_sup_right.trans hH.1.1, hH.1.2⟩)
    (hH.2.1.trans S.G1_le_centralizer_V1) (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V)
    (S.V1_le_V2.trans S.V2_le_V3)
    ((Subgroup.centralizer_le_normalizer (V : Set G)).trans S.NV_le_M) S.pCoreOf_L_le_T
    (fun _ hy _ hl => S.comm_mem_pCoreOf hy hl)
    (fun _ _ hy3 hodd => S.mem_centralizer_V_of_odd h13315 hy3 hodd)

theorem weak_e_core {g : G} (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G),
      (∀ (a : G) (ha : a ∈ conjSub g⁻¹ V), S.frame.ρ ⟨a, hN ha⟩ ∈ R8) ∧
      ∀ (a b : G) (ha : a ∈ conjSub g⁻¹ V) (hb : b ∈ conjSub g⁻¹ V),
        Quad (S.frame.ρ ⟨a, hN ha⟩) (S.frame.ρ ⟨b, hN hb⟩) := by
  have hVg : IsElemAbelian 2 (conjSub g⁻¹ V) := F7.isElemAbelian_conjSub S.elemAbelian_V
  have hcomm : ∀ a ∈ conjSub g⁻¹ V, ∀ b ∈ conjSub g⁻¹ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVg.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hva : ∀ v ∈ V, ∀ a ∈ conjSub g⁻¹ V, v * a * v⁻¹ * a⁻¹ ∈ V ⊓ conjSub g⁻¹ V :=
    fun v hv a ha => h1 (Subgroup.commutator_mem_commutator hv ha)
  have hfwd : ∀ a ∈ conjSub g⁻¹ V, ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro a ha v hv
    have h := (hva v hv a ha).1
    have e : a * v * a⁻¹ = (v * a * v⁻¹ * a⁻¹)⁻¹ * v := by group
    rw [e]
    exact V.mul_mem (V.inv_mem h) hv
  have hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hfwd a ha v, fun hv => ?_⟩
    have ha2 : a⁻¹ = a := by
      have := hVg.2 a ha
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_left this
    have haa : a * a = 1 := by
      have := hVg.2 a ha
      rwa [pow_two] at this
    have := hfwd a ha _ hv
    rwa [ha2, show a * (a * v * a) * a = (a * a) * v * (a * a) by group, haa, one_mul,
      mul_one] at this
  refine ⟨hN, ?_, ?_⟩
  · intro a ha
    have hza : a * S.z * a⁻¹ = S.z := by
      have hzg : S.z ∈ conjSub g⁻¹ V := by
        rw [mem_conjSub, inv_inv]
        have : g * S.z * g⁻¹ = S.z := by
          have := Subgroup.mem_centralizer_singleton_iff.mp hg
          calc g * S.z * g⁻¹ = S.z * g * g⁻¹ := by rw [this]
            _ = S.z := by group
        rw [this]
        exact S.z_mem_V
      rw [hcomm a ha _ hzg]
      group
    refine mem_R8 _ (S.fix_e0123 _ hza) fun x hx => ?_
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨x, hx.1⟩
    have hv3 : (v : G) ∈ S.V3 := by
      refine S.mem_pre.2 ⟨v.2, ?_⟩
      have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨x, hx.1⟩ := hv
      rw [e]
      exact hx.2
    have hc : a * v * a⁻¹ * (v : G)⁻¹ ∈ fsuV1 T V := by
      have := h2 (Subgroup.commutator_mem_commutator hv3 ha)
      have e : a * v * a⁻¹ * (v : G)⁻¹ = (v * a * (v : G)⁻¹ * a⁻¹)⁻¹ := by group
      rw [e]
      exact (fsuV1 T V).inv_mem this
    show ((act4 (S.frame.ρ ⟨a, hN ha⟩) ⟨x, hx.1⟩ * (⟨x, hx.1⟩ : ↥W4)⁻¹ : ↥W4) : P6) = 1 ∨
      ((act4 (S.frame.ρ ⟨a, hN ha⟩) ⟨x, hx.1⟩ * (⟨x, hx.1⟩ : ↥W4)⁻¹ : ↥W4) : P6) = e0123
    rw [← hv, ← S.psi_conj ⟨a, hN ha⟩ v, ← map_inv, ← map_mul]
    rcases S.mem_V1_iff.1 hc with h | h
    · left
      have : (⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hN ha) v).mp v.2⟩ * v⁻¹ : ↥V) =
          1 := Subtype.ext (by simpa using h)
      rw [this, map_one]
      rfl
    · right
      have : (⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hN ha) v).mp v.2⟩ * v⁻¹ : ↥V) =
          ⟨S.z, S.z_mem_V⟩ := Subtype.ext (by simpa using h)
      rw [this, S.psi_z]
  · intro a b ha hb x hx
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨x, hx⟩
    suffices h : act4 (S.frame.ρ ⟨b, hN hb⟩) (act4 (S.frame.ρ ⟨a, hN ha⟩) ⟨x, hx⟩ *
        (⟨x, hx⟩ : ↥W4)⁻¹) = act4 (S.frame.ρ ⟨a, hN ha⟩) ⟨x, hx⟩ * (⟨x, hx⟩ : ↥W4)⁻¹ from
      congrArg Subtype.val h
    rw [← hv, ← S.psi_conj ⟨a, hN ha⟩ v, ← map_inv, ← map_mul, ← S.psi_conj ⟨b, hN hb⟩]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hmem : a * v * a⁻¹ * (v : G)⁻¹ ∈ conjSub g⁻¹ V := by
      have := (hva v v.2 a ha).2
      have e : a * v * a⁻¹ * (v : G)⁻¹ = (v * a * (v : G)⁻¹ * a⁻¹)⁻¹ := by group
      rw [e]
      exact (conjSub g⁻¹ V).inv_mem this
    rw [hcomm b hb _ hmem]
    group

theorem weak_e_two (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G), ∀ (a b : G)
      (ha : a ∈ conjSub g⁻¹ V) (hb : b ∈ conjSub g⁻¹ V), S.frame.ρ ⟨a, hN ha⟩ = 1 ∨
        S.frame.ρ ⟨b, hN hb⟩ = 1 ∨ S.frame.ρ ⟨a, hN ha⟩ = S.frame.ρ ⟨b, hN hb⟩ := by
  obtain ⟨hN, hR, hquad⟩ := S.weak_e_core hg h1 h2
  refine ⟨hN, fun a b ha hb => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨ha1, hb1, hab⟩ := hne
  have key : ∃ (c d : G) (hc : c ∈ conjSub g⁻¹ V) (hd : d ∈ conjSub g⁻¹ V),
      S.frame.ρ ⟨c, hN hc⟩ = swap 4 5 ∧ S.frame.ρ ⟨d, hN hd⟩ ≠ 1 ∧
        S.frame.ρ ⟨d, hN hd⟩ ≠ swap 4 5 := by
    rcases quad_R8 _ (hR a ha) _ (hR b hb) ha1 hb1 hab (hquad a b ha hb) with h | h | h
    · exact ⟨a, b, ha, hb, h, hb1, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨b, a, hb, ha, h, ha1, fun h' => hab (h'.trans h.symm)⟩
    · refine ⟨a * b, a, (conjSub g⁻¹ V).mul_mem ha hb, ha, ?_, ha1, fun h' => ?_⟩
      · rw [← h, ← map_mul]
        rfl
      · apply hb1
        rw [h'] at h
        exact mul_left_cancel (h.trans (mul_one _).symm)
  obtain ⟨c, d, hc, hd, hct, hd1, hdt⟩ := key
  obtain ⟨π, hπC, hπ⟩ := synWit _ (hR d hd) hd1 hdt
  obtain ⟨l, -, hl⟩ := (S.frame.image_L π).2 (Perm.mem_alternatingGroup.2 (C3_sign π hπC))
  have hV2 : S.V2 ≤ V ⊓ conjSub (g * l)⁻¹ V := by
    intro w hw
    obtain ⟨hwV, hwW2⟩ := S.mem_pre.1 hw
    refine Subgroup.mem_inf.2 ⟨hwV, ?_⟩
    obtain ⟨x, hx, hxe⟩ := hπ _ hwW2
    set v : ↥V := S.frame.ψ.symm ⟨x, hx⟩
    have hdv : (d : G) * v * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hN hd) v).mp v.2
    have heq : (l : G) * w * (l : G)⁻¹ = v * d * (v : G)⁻¹ * d⁻¹ := by
      have h1' := S.psi_conj l ⟨w, hwV⟩
      rw [hl] at h1'
      have h2' : S.frame.ψ ⟨v * d * (v : G)⁻¹ * d⁻¹, by
          have e : (v : G) * d * (v : G)⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
          rw [e]
          exact V.mul_mem v.2 (V.inv_mem hdv)⟩ =
          S.frame.ψ v * (act4 (S.frame.ρ ⟨d, hN hd⟩) (S.frame.ψ v))⁻¹ := by
        rw [← S.psi_conj ⟨d, hN hd⟩ v, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h3' : S.frame.ψ ⟨(l : G) * w * (l : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp l.2 w).mp hwV⟩ = S.frame.ψ ⟨v * d * (v : G)⁻¹ * d⁻¹,
          by
            have e : (v : G) * d * (v : G)⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
            rw [e]
            exact V.mul_mem v.2 (V.inv_mem hdv)⟩ := by
        rw [h1', h2', MulEquiv.apply_symm_apply]
        exact Subtype.ext hxe
      exact congrArg Subtype.val (S.frame.ψ.injective h3')
    have hmemA : (l : G) * w * (l : G)⁻¹ ∈ conjSub g⁻¹ V := by
      rw [heq]
      exact (h1 (Subgroup.commutator_mem_commutator v.2 hd)).2
    rw [mem_conjSub, inv_inv] at hmemA ⊢
    have e : g * l * w * (g * l)⁻¹ = g * ((l : G) * w * (l : G)⁻¹) * g⁻¹ := by group
    rw [e]
    exact hmemA
  have hcN : (l : G)⁻¹ * c * l ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ l.2) (hN hc)) l.2
  have hc' : (l : G)⁻¹ * c * l ∈ conjSub (g * l)⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have hcA := hc
    rw [mem_conjSub, inv_inv] at hcA
    have e : g * l * ((l : G)⁻¹ * c * l) * (g * l)⁻¹ = g * c * g⁻¹ := by group
    rw [e]
    exact hcA
  have hρc' : S.frame.ρ ⟨(l : G)⁻¹ * c * l, hcN⟩ = π⁻¹ * swap 4 5 * π := by
    have e : (⟨(l : G)⁻¹ * c * l, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        l⁻¹ * ⟨c, hN hc⟩ * l := rfl
    rw [e, map_mul, map_mul, map_inv, hct, hl]
  have hsign : Perm.sign (π⁻¹ * swap 4 5 * π) = -1 := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, t_facts.2.1, C3_sign π hπC]
    simp
  rcases S.lemma13_5_6_three hNS h1356two h13315 (g * l) hV2 with h0 | ⟨-, -, hauto⟩
  ·
    have hcC : (l : G)⁻¹ * c * l ∈ Subgroup.centralizer (V : Set G) := by
      have : conjSub (g * l)⁻¹ V ≤ Subgroup.centralizer (V : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h0
      exact this hc'
    have h1c := (S.rho_eq_one_iff ⟨_, hcN⟩).2 hcC
    rw [hρc'] at h1c
    rw [h1c, Perm.sign_one] at hsign
    exact absurd hsign (by decide)
  ·
    have hmem : conjAct V ⟨_, hcN⟩ ∈ autOn (conjSub (g * l)⁻¹ V) V := ⟨⟨_, hcN⟩, hc', rfl⟩
    obtain ⟨x, hxL2, hx⟩ := hauto hmem
    have hxL : (x : G) ∈ L := ((oTwoRes_le _).trans inf_le_left) hxL2
    have hρx := S.rho_eq_of_conjAct_eq hx
    have hev := (S.frame.image_L _).1 ⟨x, hxL, rfl⟩
    rw [hρx, hρc', Perm.mem_alternatingGroup] at hev
    rw [hev] at hsign
    exact absurd hsign (by decide)

theorem weak_e_card (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) :
    Nat.card (conjSub g⁻¹ V) ≤
      2 * Nat.card ↥(conjSub g⁻¹ V ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨hN, hσ⟩ := S.weak_e_two hNS h1356two h13315 hg h1 h2
  set A := conjSub g⁻¹ V
  let φ : ↥A →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hN)
  have hker : ∀ a : ↥A, φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := fun a =>
    S.rho_eq_one_iff _
  have hrange : Nat.card φ.range ≤ 2 := by
    by_cases hex : ∃ a : ↥A, φ a ≠ 1
    · obtain ⟨a₀, ha₀⟩ := hex
      have hsub : (φ.range : Set (Perm (Fin 6))) ⊆ {1, φ a₀} := by
        rintro _ ⟨b, rfl⟩
        rcases hσ a₀ b a₀.2 b.2 with h | h | h
        · exact absurd h ha₀
        · exact Or.inl h
        · exact Or.inr h.symm
      calc Nat.card φ.range = Nat.card ((φ.range : Set (Perm (Fin 6)))) := rfl
        _ ≤ Nat.card (({1, φ a₀} : Set (Perm (Fin 6)))) :=
          Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
    · push Not at hex
      have : φ.range = ⊥ := by
        ext σ
        constructor
        · rintro ⟨b, rfl⟩
          exact hex b
        · intro h
          rw [Subgroup.mem_bot] at h
          exact ⟨1, by rw [h, map_one]⟩
      rw [this, Subgroup.card_bot]
      norm_num
  have hkcard : Nat.card φ.ker = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_congr ⟨fun a => ⟨a.1, a.1.2, (hker a.1).1 a.2⟩,
      fun b => ⟨⟨b.1, b.2.1⟩, (hker ⟨b.1, b.2.1⟩).2 b.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have h := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hkcard] at h
  calc Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * Nat.card φ.range :=
        h.symm
    _ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring

theorem card_inf_centralizer_le_four {a : G} (haN : a ∈ Subgroup.normalizer (V : Set G))
    (hR : S.frame.ρ ⟨a, haN⟩ ∈ R8) (h1 : S.frame.ρ ⟨a, haN⟩ ≠ 1)
    (ht : S.frame.ρ ⟨a, haN⟩ ≠ swap 4 5) {A : Subgroup G} (haA : a ∈ A) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 := by
  rw [← card_fix_R8 _ hR h1 ht, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective
    (fun v => ⟨(S.frame.ψ ⟨v.1, (Subgroup.mem_inf.1 v.2).1⟩ : P6), (S.frame.ψ _).2, ?_⟩) ?_
  · have hc := (S.conj_eq_iff ⟨a, haN⟩ ⟨v.1, (Subgroup.mem_inf.1 v.2).1⟩).1 (by
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 v.2).2 a haA
      calc a * v.1 * a⁻¹ = v.1 * a * a⁻¹ := by rw [this]
        _ = v.1 := by group)
    exact congrArg Subtype.val hc
  · intro v w h
    have h' := congrArg Subtype.val h
    dsimp only at h'
    have := S.frame.ψ.injective (Subtype.ext h')
    exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem rho_one_or_t (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) (h3 : ⁅conjSub g⁻¹ S.V3, V⁆ ≤ fsuV1 T V) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G), ∀ (a : G) (ha : a ∈ conjSub g⁻¹ V),
      S.frame.ρ ⟨a, hN ha⟩ = 1 ∨ S.frame.ρ ⟨a, hN ha⟩ = swap 4 5 := by
  obtain ⟨hN, hR, -⟩ := S.weak_e_core hg h1 h2
  refine ⟨hN, fun a ha => ?_⟩
  by_contra hne
  push Not at hne
  have h4 := S.card_inf_centralizer_le_four (hN ha) (hR a ha) hne.1 hne.2 ha
  have hginv : g⁻¹ ∈ S.G1 := S.G1.inv_mem hg
  have hgN1 : g ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.G1_le_normalizer_V1 hg
  have h1' : ⁅V, conjSub g⁻¹⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹⁻¹ V := by
    rw [inv_inv]
    have := conjSub_mono g h1
    rw [← conjSub_commutator, conjSub_inv_conjSub, conjSub_inf, conjSub_inv_conjSub,
      Subgroup.commutator_comm] at this
    rwa [inf_comm]
  have h2' : ⁅S.V3, conjSub g⁻¹⁻¹ V⁆ ≤ fsuV1 T V := by
    rw [inv_inv]
    have := conjSub_mono g h3
    rwa [← conjSub_commutator, conjSub_inv_conjSub, A5.conjSub_self_of_mem hgN1] at this
  have hF1 := S.weak_e_card hNS h1356two h13315 hginv h1' h2'
  rw [inv_inv, A5.card_conjSub', S.card_V] at hF1
  have htrans : Nat.card ↥(conjSub g V ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G)) := by
    have e : conjSub g⁻¹ (conjSub g V ⊓ Subgroup.centralizer (V : Set G)) =
        V ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G) := by
      rw [conjSub_inf, conjSub_conjSub_inv, conjSub_centralizer]
    rw [← e, A5.card_conjSub']
  rw [htrans] at hF1
  omega

theorem weak_e (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) (h3 : ⁅conjSub g⁻¹ S.V3, V⁆ ≤ fsuV1 T V) :
    ⁅S.V3, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ S.V3, V⁆ = ⊥ := by
  have hginv : g⁻¹ ∈ S.G1 := S.G1.inv_mem hg
  have hgN1 : g ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.G1_le_normalizer_V1 hg
  have h1' : ⁅V, conjSub g⁻¹⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹⁻¹ V := by
    rw [inv_inv]
    have := conjSub_mono g h1
    rw [← conjSub_commutator, conjSub_inv_conjSub, conjSub_inf, conjSub_inv_conjSub,
      Subgroup.commutator_comm] at this
    rwa [inf_comm]
  have h2' : ⁅S.V3, conjSub g⁻¹⁻¹ V⁆ ≤ fsuV1 T V := by
    rw [inv_inv]
    have := conjSub_mono g h3
    rwa [← conjSub_commutator, conjSub_inv_conjSub, A5.conjSub_self_of_mem hgN1] at this
  have h3' : ⁅conjSub g⁻¹⁻¹ S.V3, V⁆ ≤ fsuV1 T V := by
    rw [inv_inv]
    have := conjSub_mono g h2
    rwa [← conjSub_commutator, conjSub_inv_conjSub, A5.conjSub_self_of_mem hgN1] at this
  have hcen : ∀ k : G, k ∈ S.G1 → ⁅V, conjSub k⁻¹ V⁆ ≤ V ⊓ conjSub k⁻¹ V →
      ⁅S.V3, conjSub k⁻¹ V⁆ ≤ fsuV1 T V → ⁅conjSub k⁻¹ S.V3, V⁆ ≤ fsuV1 T V →
      conjSub k⁻¹ V ≤ Subgroup.centralizer (S.V3 : Set G) := by
    intro k hk h1k h2k h3k a ha
    obtain ⟨hN, hσ⟩ := S.rho_one_or_t hNS h1356two h13315 hk h1k h2k h3k
    refine S.centralizer_of_fixW3 (x := ⟨a, hN ha⟩) ?_
    rcases hσ a ha with h | h <;> rw [h]
    · exact fun x hx => act4f_one x hx.1
    · exact t_facts.1
  have hA := hcen g hg h1 h2 h3
  have hA' : conjSub g V ≤ Subgroup.centralizer (S.V3 : Set G) := by
    have := hcen g⁻¹ hginv h1' h2' h3'
    rwa [inv_inv] at this
  constructor
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hA
  · have h0 : ⁅conjSub g V, S.V3⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hA'
    have := congrArg (conjSub g⁻¹) h0
    rw [← conjSub_commutator, conjSub_conjSub_inv, conjSub_bot, Subgroup.commutator_comm] at this
    exact this

theorem hypF91
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    HypF91 T V L (fsuV1 T V) S.V3 H :=
  hypF91_of S.h13.sylow S.h13.faithful S.h13.qtke.2.1 S.T_le_NL S.reduced S.cT S.uniqueM
    S.card_V1 S.V1_lt_V3 S.V3_le_V S.T_le_NV1 hH.1 (hH.2.1.trans S.G1_le_centralizer_V1)
    hH.2.2 (S.coreIn_le_pCoreOf h13315 hH) S.L1T_le_NV3 S.irred_V3
    (fun _ hx => S.G1_inf_G3_le h13315 ⟨hH.2.1 hx.1, hx.2⟩)
    (fun _ hg h1 h2 h3 => S.weak_e hNS h1356two h13315 (hH.2.1 hg) h1 h2 h3)

end Setting4

end CFSG.Quasithin.H13.A6
