module

public import CFSG.Quasithin.Background.Harris.R1.QbetaKer
public import CFSG.Quasithin.Recognition.SzR1Enum
public import CFSG.Quasithin.Recognition.SzR1Prep

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem invol_mem_V [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hc5 : Fintype.card Ω = 5) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {r : G} (hrW : r ∈ vBeta K1 L2 S Zs) (hr2 : r * r = 1)
    (hrc : r * C.zf C.D.pt = C.zf C.D.pt * r) : r ∈ conjClosure Zs L2 := by
  classical
  have hodd : Odd (Fintype.card Ω) := ⟨2, by omega⟩
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  have hclos : ∀ g : ↥(vBeta K1 L2 S Zs),
      g ∈ Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    intro g
    rw [C.closure_wU hij]
    exact Subgroup.mem_top g
  have hyUc : ∀ g : ↥(vBeta K1 L2 S Zs),
      g * gprod C.wU l₀ = gprod C.wU l₀ * g := fun g =>
    hG.commute_gprod_univ_closure hodd l₀ hl₀ hall (hclos g)
  have hyZ : ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∈ Zs := by
    refine hcen _ (gprod C.wU l₀).2 fun u hu => ?_
    exact (congrArg Subtype.val (hyUc ⟨u, hu⟩)).symm
  obtain ⟨i, j, k, hijk⟩ := hG.sq_eq_one_comm_mem hz hc5 C.D.pt l₀ hl₀ hall (hclos ⟨r, hrW⟩)
    (Subtype.ext hr2) (Subtype.ext hrc)
  have hr' : r = (C.cm i₀ j₀) ^ i * (C.zf C.D.pt) ^ j *
      ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ^ k := by
    have h1 := congrArg Subtype.val hijk
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      Subgroup.coe_pow] at h1
    exact h1
  have hV : conjClosure Zs L2 = C.D.Vf (conjClosure Zs L2) C.D.pt := C.Vf_pt.symm
  have hzV : C.cm i₀ j₀ ^ i ∈ conjClosure Zs L2 :=
    le_conjClosure Zs L2 (Zs.pow_mem (C.cm_mem i₀ j₀) i)
  have hptV : C.zf C.D.pt ^ j ∈ conjClosure Zs L2 := by
    refine (conjClosure Zs L2).pow_mem ?_ j
    rw [hV]
    exact C.zf_mem C.D.pt
  have hyV : ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ^ k ∈ conjClosure Zs L2 :=
    le_conjClosure Zs L2 (Zs.pow_mem hyZ k)
  rw [hr']
  exact (conjClosure Zs L2).mul_mem ((conjClosure Zs L2).mul_mem hzV hptV) hyV

namespace FamCtxPar

variable (C : FamCtx K1 L2 S Zs Ω)

open Classical in
noncomputable def bit (x : G) : Bool := decide (x ≠ 1)

noncomputable def rho (k : Ω) (x : G) : G := C.zf k * x * (C.zf k)⁻¹ * x⁻¹

include C

theorem rho_mem (k : Ω) {x : G} (hx : x ∈ vBeta K1 L2 S Zs) : rho C k x ∈ Zs :=
  C.U_comm_mem (C.zf_mem_U k) hx

theorem rho_mul (k : Ω) {x y : G} (hx : x ∈ vBeta K1 L2 S Zs) (hy : y ∈ vBeta K1 L2 S Zs) :
    rho C k (x * y) = rho C k x * rho C k y := by
  have hc : x * rho C k y = rho C k y * x := C.Zs_central hx (rho_mem C k hy)
  calc rho C k (x * y) = (C.zf k * x * (C.zf k)⁻¹ * x⁻¹) * (x * (C.zf k * y * (C.zf k)⁻¹ * y⁻¹) * x⁻¹) := by
        unfold rho; group
    _ = rho C k x * (x * rho C k y * x⁻¹) := rfl
    _ = rho C k x * rho C k y := by rw [hc]; group

theorem rho_central (k : Ω) {c : G} (hc : c ∈ Zs) : rho C k c = 1 := by
  have := C.Zs_central (C.zf_mem_U k) hc
  unfold rho
  rw [this]
  group

theorem rho_zf [DecidableEq Ω] {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (k a : Ω) :
    rho C k (C.zf a) = if a = k then 1 else C.cm i₀ j₀ := by
  by_cases hak : a = k
  · subst hak
    rw [if_pos rfl]
    unfold rho
    group
  · rw [if_neg hak]
    exact C.cm_const hij (fun h => hak h.symm)

omit C in
theorem bit_mul {z0 : G} (hz0 : z0 ≠ 1) (hz2 : z0 * z0 = 1) {u w : G} (hu : u = 1 ∨ u = z0)
    (hw : w = 1 ∨ w = z0) : bit (u * w) = xor (bit u) (bit w) := by
  classical
  unfold bit
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> simp [hz0, hz2]

theorem pattern [Fintype Ω] [DecidableEq Ω] {i₀ j₀ : Ω} (hij₀ : i₀ ≠ j₀) {a' : G} (ha'S : a' ∈ S)
    {σ : Ω → Ω} {c : Ω → G} (hcZ : ∀ i, c i ∈ Zs)
    (hcE : ∀ i, a' * C.zf i * a'⁻¹ = C.zf (σ i) * c i) {i j : Ω}
    (hv : a' * (C.zf i * C.zf j) * a'⁻¹ * (C.zf i * C.zf j)⁻¹ ∈ conjClosure Zs L2) :
    ∃ f : Bool, ∀ k : Ω, k ≠ C.D.pt →
      xor (decide (σ i = k)) (decide (σ j = k)) =
        xor f (xor (decide (i = k)) (decide (j = k))) := by
  classical
  set z0 := C.cm i₀ j₀ with hz0
  have hz0Z : z0 ∈ Zs := C.cm_mem i₀ j₀
  have hz01 : z0 ≠ 1 := C.cm_ne_one hij₀
  have hz02 : z0 * z0 = 1 := C.Zs_sq hz0Z
  have hZc : ∀ u ∈ Zs, u = 1 ∨ u = z0 := fun u hu => Zs_eq_one_or C hij₀ hu
  set x := C.zf i * C.zf j with hx
  have hxW : x ∈ vBeta K1 L2 S Zs := (vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j)
  set v := a' * x * a'⁻¹ * x⁻¹ with hvdef
  have hvW : v ∈ vBeta K1 L2 S Zs := le_conjClosure (conjClosure Zs L2) (K1 ⊔ S) hv
  have hx' : a' * x * a'⁻¹ = (C.zf (σ i) * c i) * (C.zf (σ j) * c j) := by
    have e : a' * x * a'⁻¹ = (a' * C.zf i * a'⁻¹) * (a' * C.zf j * a'⁻¹) := by rw [hx]; group
    rw [e, hcE i, hcE j]
  have hxv : a' * x * a'⁻¹ = v * x := by rw [hvdef]; group
  have hzc : ∀ m, C.zf (σ m) * c m ∈ vBeta K1 L2 S Zs := fun m =>
    (vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U (σ m)) (F112J2.Zs_le_vBeta K1 L2 S Zs (hcZ m))
  have hrhoz : ∀ (k m : Ω), rho C k (C.zf (σ m) * c m) = rho C k (C.zf (σ m)) := by
    intro k m
    rw [rho_mul C k (C.zf_mem_U (σ m)) (F112J2.Zs_le_vBeta K1 L2 S Zs (hcZ m)),
      rho_central C k (hcZ m), mul_one]
  have hrho : ∀ k : Ω, rho C k (a' * x * a'⁻¹) =
      rho C k (C.zf (σ i)) * rho C k (C.zf (σ j)) := by
    intro k
    rw [hx', rho_mul C k (hzc i) (hzc j), hrhoz k i, hrhoz k j]
  have hrho2 : ∀ k : Ω, rho C k (a' * x * a'⁻¹) = rho C k v * (rho C k (C.zf i) * rho C k (C.zf j)) := by
    intro k
    rw [hxv, rho_mul C k hvW hxW, hx, rho_mul C k (C.zf_mem_U i) (C.zf_mem_U j)]
  have hf : ∃ f : Bool, ∀ k : Ω, k ≠ C.D.pt → bit (rho C k v) = f := by
    have hvV : v ∈ C.D.Vf (conjClosure Zs L2) C.D.pt := by rw [C.Vf_pt]; exact hv
    rcases C.Vf_eq hvV with h1 | h1
    · refine ⟨false, fun k _ => ?_⟩
      have : rho C k v = 1 := rho_central C k h1
      simp [bit, this]
    · refine ⟨true, fun k hk => ?_⟩
      have hv' : v = C.zf C.D.pt * ((C.zf C.D.pt)⁻¹ * v) := by group
      have hc' : (C.zf C.D.pt)⁻¹ * v ∈ Zs := h1
      have : rho C k v = z0 := by
        rw [hv', rho_mul C k (C.zf_mem_U _) (F112J2.Zs_le_vBeta K1 L2 S Zs hc'),
          rho_central C k hc', mul_one, rho_zf C hij₀ k, if_neg (fun h => hk h.symm)]
      simp [bit, this, hz01]
  obtain ⟨f, hfk⟩ := hf
  refine ⟨f, fun k hk => ?_⟩
  have e := hrho2 k
  rw [hrho k] at e
  have hzmem : ∀ m, rho C k (C.zf m) = if m = k then 1 else z0 := rho_zf C hij₀ k
  have hb := congrArg bit e
  have hrv : rho C k v ∈ Zs := rho_mem C k hvW
  have hcase : ∀ m, rho C k (C.zf m) = 1 ∨ rho C k (C.zf m) = z0 := by
    intro m
    rw [hzmem m]
    split_ifs <;> simp
  rw [bit_mul hz01 hz02 (hcase _) (hcase _), bit_mul hz01 hz02 (hZc _ hrv)
    (by
      have h1 := hcase i; have h2 := hcase j
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> simp [hz02]),
    bit_mul hz01 hz02 (hcase _) (hcase _), hfk k hk] at hb
  have hbz : ∀ m, bit (rho C k (C.zf m)) = decide (m ≠ k) := by
    intro m
    rw [hzmem m]
    by_cases h : m = k <;> simp [h, bit, hz01]
  rw [hbz, hbz, hbz, hbz] at hb
  revert hb
  by_cases h1 : σ i = k <;> by_cases h2 : σ j = k <;> by_cases h3 : i = k <;> by_cases h4 : j = k <;>
    cases f <;> simp [h1, h2, h3, h4]

theorem Vf_inj {i j : Ω} (h : C.D.Vf (conjClosure Zs L2) i = C.D.Vf (conjClosure Zs L2) j) :
    i = j := by
  by_contra hne
  have hj : C.zf j ∈ C.D.Vf (conjClosure Zs L2) i := by rw [h]; exact C.zf_mem j
  rcases C.Vf_eq hj with h1 | h1
  · exact C.zf_not_mem j h1
  · apply C.cm_ne_one hne
    have hc : C.zf j = C.zf i * ((C.zf i)⁻¹ * C.zf j) := by group
    have hcen : (C.zf i)⁻¹ * C.zf j * C.zf i = C.zf i * ((C.zf i)⁻¹ * C.zf j) :=
      (C.Zs_central (C.zf_mem_U i) h1).symm
    unfold FamCtx.cm
    rw [hc]
    calc C.zf i * (C.zf i * ((C.zf i)⁻¹ * C.zf j)) * (C.zf i)⁻¹ *
          (C.zf i * ((C.zf i)⁻¹ * C.zf j))⁻¹
        = C.zf i * (C.zf i * ((C.zf i)⁻¹ * C.zf j)) * (C.zf i)⁻¹ *
          (((C.zf i)⁻¹ * C.zf j)⁻¹ * (C.zf i)⁻¹) := by group
      _ = 1 := by
        set c := (C.zf i)⁻¹ * C.zf j
        have h2 : C.zf i * c = c * C.zf i := (C.Zs_central (C.zf_mem_U i) h1)
        calc C.zf i * (C.zf i * c) * (C.zf i)⁻¹ * (c⁻¹ * (C.zf i)⁻¹)
            = C.zf i * (c * C.zf i) * (C.zf i)⁻¹ * (c⁻¹ * (C.zf i)⁻¹) := by rw [h2]
          _ = 1 := by group

end FamCtxPar

theorem V4_of_pairs (σ : Fin 5 → Fin 5) (hinj : Function.Injective σ) (h4 : σ 4 = 4)
    (hp : ∀ j : Fin 5, j ≠ 0 → j ≠ 4 → ∃ f : Bool, ∀ k : Fin 5, k ≠ 4 →
      xor (decide (σ 0 = k)) (decide (σ j = k)) =
        xor f (xor (decide ((0 : Fin 5) = k)) (decide (j = k)))) :
    ∃ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 ∧ τ 4 = 4 ∧ τ * τ = 1 ∧ ∀ i, τ i = σ i := by
  revert σ
  decide +kernel

open FamCtxPar in
theorem parity (C : FamCtx K1 L2 S Zs (Fin 5)) (hpt : C.D.pt = 4)
    (hsurj : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ 4 = 4 → τ * τ = 1 →
      ∃ k : ↥K1, (k : G) ∈ S ∧ ∀ i, C.D.act k i = τ i)
    {a' : G} (ha'S : a' ∈ S)
    (hAV : ∀ x ∈ vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S), x * a' * x⁻¹ * a'⁻¹ ∈ conjClosure Zs L2) :
    ∃ k ∈ K1, k ∈ S ∧ k⁻¹ * a' ∈ C.kerM := by
  classical
  have hij₀ : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨σ, c, hcZ, hcE, hσ⟩ := C.exists_sigma ha'S
  have hinj : Function.Injective σ := fun i j hij => by
    apply Vf_inj C
    have : conjSub a' (C.D.Vf (conjClosure Zs L2) i) = conjSub a' (C.D.Vf (conjClosure Zs L2) j) := by
      rw [hσ i, hσ j, hij]
    exact (conjSub_inj a').mp this
  have hV4 : C.D.Vf (conjClosure Zs L2) 4 = conjClosure Zs L2 := by
    rw [← hpt]
    exact C.Vf_pt
  have hσpt : σ 4 = 4 := by
    apply Vf_inj C
    calc C.D.Vf (conjClosure Zs L2) (σ 4) = conjSub a' (C.D.Vf (conjClosure Zs L2) 4) :=
          (hσ 4).symm
      _ = conjSub a' (conjClosure Zs L2) := by rw [hV4]
      _ = conjClosure Zs L2 := F7.conjSub_eq_of_mem_normalizer (C.hSV ha'S)
      _ = C.D.Vf (conjClosure Zs L2) 4 := hV4.symm
  have hp : ∀ j : Fin 5, j ≠ 0 → j ≠ 4 → ∃ f : Bool, ∀ k : Fin 5, k ≠ 4 →
      xor (decide (σ 0 = k)) (decide (σ j = k)) =
        xor f (xor (decide ((0 : Fin 5) = k)) (decide (j = k))) := by
    intro j hj0 hj4
    have hi4 : (0 : Fin 5) ≠ C.D.pt := by rw [hpt]; decide
    have hj4' : j ≠ C.D.pt := by rw [hpt]; exact hj4
    have hxW : C.zf 0 * C.zf j ∈ vBeta K1 L2 S Zs :=
      (vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U 0) (C.zf_mem_U j)
    have hxQ : C.zf 0 * C.zf j ∈ pCoreOf 2 (L2 ⊔ S) := C.zf_mul_mem_pCore hi4 hj4'
    have hv := hAV _ ⟨hxW, hxQ⟩
    have hv' : a' * (C.zf 0 * C.zf j) * a'⁻¹ * (C.zf 0 * C.zf j)⁻¹ ∈ conjClosure Zs L2 := by
      have := (conjClosure Zs L2).inv_mem hv
      have e : ((C.zf 0 * C.zf j) * a' * (C.zf 0 * C.zf j)⁻¹ * a'⁻¹)⁻¹ =
          a' * (C.zf 0 * C.zf j) * a'⁻¹ * (C.zf 0 * C.zf j)⁻¹ := by group
      rwa [e] at this
    obtain ⟨f, hf⟩ := pattern C hij₀ ha'S hcZ hcE hv'
    exact ⟨f, fun k hk => hf k (by rw [hpt]; exact hk)⟩
  obtain ⟨τ, hτ, hτ4, hτ2, hτσ⟩ := V4_of_pairs σ hinj hσpt hp
  obtain ⟨k, hkS, hk⟩ := hsurj τ hτ hτ4 hτ2
  refine ⟨(k : G), k.2, hkS, ?_⟩
  rw [C.mem_kerM]
  refine ⟨(K1 ⊔ S).mul_mem ((K1 ⊔ S).inv_mem (Subgroup.mem_sup_left k.2))
    (Subgroup.mem_sup_right ha'S), fun ω => ?_⟩
  have h1 : conjSub ((k : G)⁻¹ * a') (C.D.Vf (conjClosure Zs L2) ω) =
      conjSub (k : G)⁻¹ (conjSub a' (C.D.Vf (conjClosure Zs L2) ω)) := conjSub_mul _ _ _
  rw [h1, hσ ω]
  have h2 := C.D.conjSub_Vf C.hVn k⁻¹ (σ ω)
  have h3 : C.D.act k⁻¹ (σ ω) = ω := by
    rw [map_inv]
    have : C.D.act k ω = σ ω := (hk ω).trans (hτσ ω)
    rw [← this]
    exact Equiv.symm_apply_apply _ _
  rw [h3] at h2
  exact h2


end CFSG.Quasithin.Background.Harris.R1
