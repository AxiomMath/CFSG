module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigNat
public import CFSG.Holt.H78.AltModelAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Card
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]


theorem s16c11_big_symRealizes {n : ℕ} (h5 : 5 ≤ n) (h6 : n ≠ 6)
    {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) : (FFModel.symDn n).Realizes L₀ J₀ ⊥ := by

  classical
  have hcard : Nat.card ↥L₀ = 2 * Nat.card ↥L :=
    s16e_card_eq_two_mul_of_isSym_isAlt (by omega) h.sym h.alt
  have hnormal : ∀ x ∈ L₀, L.map (MulAut.conj x).toMonoidHom = L :=
    s16c11_map_conj_eq_of_card_two_mul h.ll₀ hcard
  have hnormal' : ∀ x ∈ L₀, L.map ((MulAut.conj x) : MulAut W →* MulAut W) = L := by
    intro x hx
    have heq : ((MulAut.conj x) : MulAut W →* MulAut W) = (MulAut.conj x).toMonoidHom :=
      MonoidHom.ext (fun _ => rfl)
    rw [heq]
    exact hnormal x hx
  have hcomm := s16c11_comm_of_isInternalDirect h.dir
  obtain ⟨ρ, β, hβ⟩ := s16c11_big_realizes_equiv (FFModel.altDn_isActionModel n)
    (FFC.altDn_faithful h5) h.nat₀
  let ρ' : ↥(alternatingGroup (Fin n)) ≃* ↥L := ρ
  let symA : Equiv.Perm (Fin n) →* MulAut (FFModel.symDn n).Mod :=
    (FFModel.symDn_isActionModel n).modAct
  let altAs : ↥(alternatingGroup (Fin n)) →* MulAut (FFModel.symDn n).Mod :=
    (FFModel.altDn_isActionModel n).modAct
  let βs : ↥J₀ ≃* (FFModel.symDn n).Mod :=
    { toFun := fun u => (β u : (FFModel.symDn n).Mod)
      invFun := fun q => β.symm (q : (FFModel.altDn n).Mod)
      left_inv := fun u => β.left_inv u
      right_inv := fun q => β.right_inv (q : (FFModel.altDn n).Mod)
      map_mul' := fun u v => β.map_mul u v }
  have modAct_alt : ∀ (a : ↥(alternatingGroup (Fin n))) (q : (FFModel.symDn n).Mod),
      altAs a q = symA (a : Equiv.Perm (Fin n)) q := by
    intro a q
    induction q using QuotientGroup.induction_on with
    | _ m =>
      change QuotientGroup.mk ((FFModel.altDn_isActionModel n).actSec a m)
          = QuotientGroup.mk ((FFModel.symDn_isActionModel n).actSec
              (a : Equiv.Perm (Fin n)) m)
      exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  have beta_apply : ∀ (a : ↥(alternatingGroup (Fin n))) (u : ↥J₀),
      βs (⟨((ρ' a : ↥L) : MulAut W) (u : W), h.stable _ (h.ll₀ (ρ' a).2) _ u.2⟩ : ↥J₀)
        = altAs a (βs u) := by
    intro a u
    have hb := hβ (a : (FFModel.altDn n).Gam) u
    have hsymm : (⟨((ρ' a : ↥L) : MulAut W) (u : W),
        h.stable _ (h.ll₀ (ρ' a).2) _ u.2⟩ : ↥J₀)
        = β.symm ((FFModel.altDn_isActionModel n).modAct a (β u)) := by
      apply Subtype.ext
      exact hb.symm
    change (β (⟨((ρ' a : ↥L) : MulAut W) (u : W),
        h.stable _ (h.ll₀ (ρ' a).2) _ u.2⟩ : ↥J₀) : (FFModel.symDn n).Mod)
        = altAs a (βs u)
    rw [hsymm, MulEquiv.apply_symm_apply]
    rfl
  have hmap : ∀ x : ↥L₀, J₀.map ((x : MulAut W) : W →* W) = J₀ := by
    intro x
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact h.stable x x.2 z hz
    · exact le_of_eq (Nat.card_congr
        (MulEquiv.subgroupMap (x : MulAut W) J₀).toEquiv)
  let st : ∀ x : ↥L₀, ↥J₀ ≃* ↥J₀ := fun x =>
    (MulEquiv.subgroupMap (x : MulAut W) J₀).trans (MulEquiv.subgroupCongr (hmap x))
  have st_apply : ∀ (x : ↥L₀) (u : ↥J₀), ((st x u : ↥J₀) : W) = (x : MulAut W) (u : W) :=
    fun x u => rfl
  have st_eq : ∀ (y : ↥L₀) (w : ↥J₀),
      st y w = (⟨(y : MulAut W) (w : W), h.stable y y.2 w w.2⟩ : ↥J₀) := fun y w => rfl
  have st_mul : ∀ (x y : ↥L₀) (u : ↥J₀), st (x * y) u = st x (st y u) := by
    intro x y u
    apply Subtype.ext
    rw [st_apply, st_apply, st_apply]
    rfl
  have st_one : ∀ u : ↥J₀, st 1 u = u := by
    intro u
    apply Subtype.ext
    rw [st_apply]
    rfl
  let conjL : ∀ x : ↥L₀, ↥L ≃* ↥L := fun x =>
    (MulEquiv.subgroupMap (MulAut.conj (x : MulAut W)) L).trans
      (MulEquiv.subgroupCongr (hnormal' x x.2))
  have conjL_apply : ∀ (x : ↥L₀) (l : ↥L),
      ((conjL x l : ↥L) : MulAut W) = (x : MulAut W) * (l : MulAut W) * (x : MulAut W)⁻¹ := by
    intro x l
    change (((MulEquiv.subgroupCongr (hnormal' x x.2))
      ((MulEquiv.subgroupMap (MulAut.conj (x : MulAut W)) L) l) : ↥L) : MulAut W)
      = (x : MulAut W) * (l : MulAut W) * (x : MulAut W)⁻¹
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  let phi : ∀ x : ↥L₀, MulAut ↥(alternatingGroup (Fin n)) := fun x =>
    (ρ'.trans (conjL x)).trans ρ'.symm
  have phi_apply : ∀ (x : ↥L₀) (a : ↥(alternatingGroup (Fin n))),
      ((ρ' (phi x a) : ↥L) : MulAut W)
        = (x : MulAut W) * ((ρ' a : ↥L) : MulAut W) * (x : MulAut W)⁻¹ := by
    intro x a
    have h1 : ρ' (phi x a) = conjL x (ρ' a) := by
      simp only [phi, MulEquiv.trans_apply]
      exact MulEquiv.apply_symm_apply ρ' _
    rw [h1, conjL_apply]
  have key : ∀ x : ↥L₀, ∃ σ : Equiv.Perm (Fin n),
      ∀ a : ↥(alternatingGroup (Fin n)),
        ((phi x a : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = σ * a * σ⁻¹ := by
    intro x
    exact CFSG.Holt.H78.exists_perm_conj_eq_of_mulAut_alternatingGroup
      (Δ := Fin n) (by simpa using h5) (by simpa using h6) (phi x)
  have modAct_inj_orig : Function.Injective (FFModel.symDn_isActionModel n).modAct := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply FFC.symDn_faithful h5
    intro m hm
    have h1 := congrArg (fun f : MulAut (FFModel.symDn n).Mod =>
      f (QuotientGroup.mk ⟨m, hm⟩)) hγ
    simp only [MulAut.one_apply] at h1
    rw [FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (⟨(FFModel.symDn n).act γ m,
        (FFModel.symDn_isActionModel n).sec_inv γ m hm⟩ : ↥(FFModel.symDn n).sec)⁻¹
        * ⟨m, hm⟩ ∈ (FFModel.symDn n).ker.subgroupOf (FFModel.symDn n).sec := h2
    rw [Subgroup.mem_subgroupOf] at h3
    have h4 := (FFModel.symDn n).ker.inv_mem h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h4
    rw [mul_comm]
    exact h4
  have modAct_inj : Function.Injective symA := modAct_inj_orig
  have uniq : ∀ σ σ' : Equiv.Perm (Fin n),
      (∀ u : ↥J₀, symA σ (βs u) = symA σ' (βs u)) → σ = σ' := by
    intro σ σ' hσ
    have h1 : symA (σ⁻¹ * σ') = 1 := by
      ext q
      obtain ⟨u, rfl⟩ := βs.surjective q
      have hh := congrArg (symA σ⁻¹) (hσ u)
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel, map_one, MulAut.one_apply] at hh
      simpa using hh.symm
    exact inv_mul_eq_one.mp (modAct_inj (by rw [h1, map_one]))
  have theta_spec : ∀ x : ↥L₀, ∃ σ : Equiv.Perm (Fin n),
      ∀ u : ↥J₀, βs (st x u) = symA σ (βs u) := by
    intro x
    obtain ⟨σ, hσ⟩ := key x
    refine ⟨σ, ?_⟩
    let θx : ↥J₀ ≃* ↥J₀ :=
      (st x).trans (((βs.trans (symA σ⁻¹)).trans βs.symm))
    have hθu : ∀ u : ↥J₀, βs (θx u) = symA σ⁻¹ (βs (st x u)) := by
      intro u
      simp only [θx, MulEquiv.trans_apply]
      exact MulEquiv.apply_symm_apply βs _
    have hθx_comm : ∀ (l : ↥L) (u v : ↥J₀),
        (l : MulAut W) (u : W) = (v : W) →
        (l : MulAut W) ((θx u : ↥J₀) : W) = ((θx v : ↥J₀) : W) := by
      intro l u v huv
      set a : ↥(alternatingGroup (Fin n)) := ρ'.symm l with ha
      have hlsub : ρ' a = l := by rw [ha, MulEquiv.apply_symm_apply]
      let ra : ↥L₀ := ⟨(ρ' a : ↥L), h.ll₀ (ρ' a).2⟩
      have hra : (ra : MulAut W) = (l : MulAut W) := congrArg Subtype.val hlsub
      have hv : st ra u = v := by
        apply Subtype.ext
        rw [st_apply, hra]
        exact huv
      have hv' : st x v = st (x * ra) u := by
        rw [← hv, ← st_mul x ra u]
      have hconj : (x * ra : ↥L₀) = (⟨(ρ' (phi x a) : ↥L), h.ll₀ (ρ' (phi x a)).2⟩ : ↥L₀) * x := by
        apply Subtype.ext
        show (x : MulAut W) * ((ρ' a : ↥L) : MulAut W)
          = ((ρ' (phi x a) : ↥L) : MulAut W) * (x : MulAut W)
        rw [phi_apply]
        group
      have hstv : st x v = st (⟨(ρ' (phi x a) : ↥L), h.ll₀ (ρ' (phi x a)).2⟩ : ↥L₀) (st x u) := by
        rw [hv', hconj, st_mul]
      have hbeta_v : βs (st x v) = symA (σ * (a : Equiv.Perm (Fin n)) * σ⁻¹) (βs (st x u)) := by
        rw [hstv, st_eq, beta_apply (phi x a) (st x u), modAct_alt]
        rw [hσ a]
      have hbeta_l : βs (⟨(l : MulAut W) ((θx u : ↥J₀) : W),
          h.stable l (h.ll₀ l.2) ((θx u : ↥J₀) : W) (θx u).2⟩ : ↥J₀)
          = symA ((a : Equiv.Perm (Fin n)) * σ⁻¹) (βs (st x u)) := by
        have heq : (⟨(l : MulAut W) ((θx u : ↥J₀) : W),
            h.stable l (h.ll₀ l.2) ((θx u : ↥J₀) : W) (θx u).2⟩ : ↥J₀)
            = (⟨((ρ' a : ↥L) : MulAut W) ((θx u : ↥J₀) : W),
                h.stable (ρ' a) (h.ll₀ (ρ' a).2) ((θx u : ↥J₀) : W) (θx u).2⟩ : ↥J₀) :=
          Subtype.ext (congrArg (fun y : ↥L =>
            ((y : MulAut W) ((θx u : ↥J₀) : W))) hlsub.symm)
        rw [heq, beta_apply a (θx u), hθu u, modAct_alt]
        rw [← MulAut.mul_apply, ← map_mul]
      have hsym : symA σ⁻¹ (βs (st x v))
          = symA ((a : Equiv.Perm (Fin n)) * σ⁻¹) (βs (st x u)) := by
        rw [hbeta_v, ← MulAut.mul_apply, ← map_mul]
        congr 1
        group
      have hfin : βs (⟨(l : MulAut W) ((θx u : ↥J₀) : W),
          h.stable l (h.ll₀ l.2) ((θx u : ↥J₀) : W) (θx u).2⟩ : ↥J₀) = βs (θx v) := by
        rw [hbeta_l, ← hsym, hθu v]
      have hj := βs.injective hfin
      exact congrArg Subtype.val hj
    have hθx : θx = MulEquiv.refl ↥J₀ := h.e₀ θx hθx_comm
    intro u
    have h1 : θx u = u := congrArg (fun e : ↥J₀ ≃* ↥J₀ => e u) hθx
    have h3 : βs u = symA σ⁻¹ (βs (st x u)) :=
      (congrArg βs h1).symm.trans (hθu u)
    have h4 := congrArg (symA σ) h3
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h4
    simpa using h4.symm
  let θf : ↥L₀ → Equiv.Perm (Fin n) := fun x => Classical.choose (theta_spec x)
  have θf_spec : ∀ (x : ↥L₀) (u : ↥J₀), βs (st x u) = symA (θf x) (βs u) :=
    fun x => Classical.choose_spec (theta_spec x)
  have θf_one : θf 1 = 1 := by
    apply uniq (θf 1) 1
    intro u
    rw [← θf_spec 1 u, st_one]
    show (1 : MulAut (FFModel.symDn n).Mod) (βs u) = symA 1 (βs u)
    rw [map_one]
  have θf_mul : ∀ x y : ↥L₀, θf (x * y) = θf x * θf y := by
    intro x y
    apply uniq (θf (x * y)) (θf x * θf y)
    intro u
    rw [← θf_spec (x * y) u, st_mul, θf_spec x (st y u), θf_spec y u]
    rw [← MulAut.mul_apply, ← map_mul]
  have θf_eq_one : ∀ x : ↥L₀, θf x = 1 → x = 1 := by
    intro x hx
    have hfix : ∀ u : ↥J₀, st x u = u := by
      intro u
      have hh := θf_spec x u
      rw [hx] at hh
      have hh' : βs (st x u) = βs u := by
        simpa only [map_one, MulAut.one_apply] using hh
      exact βs.injective hh'
    apply Subtype.ext
    ext w
    obtain ⟨s, ψ, hs, hg⟩ := h.model
    apply ψ.injective
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [hg (x : MulAut W) (h.l₀_le x.2)
      (fun k hk => (hcomm k hk x x.2).symm) w i]
    exact (st_apply x ((ψ w).1 i)).symm.trans (congrArg Subtype.val (hfix ((ψ w).1 i)))
  let θ : ↥L₀ →* Equiv.Perm (Fin n) :=
    { toFun := θf
      map_one' := θf_one
      map_mul' := θf_mul }
  have θ_inj : Function.Injective θ := by
    intro x y hxy
    have h : θ (x * y⁻¹) = 1 := by
      rw [map_mul, hxy, map_inv, mul_inv_cancel]
    exact mul_inv_eq_one.mp (θf_eq_one (x * y⁻¹) h)
  have θ_bij : Function.Bijective θ := by
    obtain ⟨e⟩ := h.sym
    have hc : Nat.card (Equiv.Perm (Fin n)) ≤ Nat.card ↥L₀ :=
      le_of_eq (Nat.card_congr e.toEquiv).symm
    exact θ_inj.bijective_of_nat_card_le hc
  let θEquiv : ↥L₀ ≃* Equiv.Perm (Fin n) := MulEquiv.ofBijective θ θ_bij
  let π : (FFModel.symDn n).Gam →* ↥L₀ :=
    { toFun := fun γ => θEquiv.symm γ
      map_one' := map_one θEquiv.symm
      map_mul' := map_mul θEquiv.symm }
  refine ⟨π, ?_⟩
  refine ⟨MulEquiv.surjective _, bot_le, (FFModel.symDn_isActionModel n).ker_le,
    (fun x y hy => h.stable x x.2 y hy),
    (fun x z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]),
    (FFModel.symDn_isActionModel n).sec_inv,
    (FFModel.symDn_isActionModel n).ker_inv, ?_⟩
  refine ⟨βs.toMonoidHom, (fun q => βs.surjective q), ?_, ?_⟩
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro hh
      exact congrArg Subtype.val (βs.map_eq_one_iff.mp hh)
    · intro hh
      exact βs.map_eq_one_iff.mpr (Subtype.ext (by simpa using hh))
  · intro γ u m hu hm hum
    have hθπ : θf (π γ) = γ := by
      show θEquiv (θEquiv.symm γ) = γ
      exact MulEquiv.apply_symm_apply θEquiv γ
    have hL : βs (⟨((π γ : ↥L₀) : MulAut W) (u : W), hu⟩ : ↥J₀)
        = symA γ (βs u) := by
      rw [show (⟨((π γ : ↥L₀) : MulAut W) (u : W), hu⟩ : ↥J₀)
          = st (π γ) u from Subtype.ext rfl]
      rw [θf_spec (π γ) u, hθπ]
    have hsym : symA γ (βs u) = symA γ (QuotientGroup.mk m) := by
      apply congrArg (symA γ)
      exact hum
    change βs (⟨((π γ : ↥L₀) : MulAut W) (u : W), hu⟩ : ↥J₀)
      = QuotientGroup.mk ⟨(FFModel.symDn n).act γ (m : (FFModel.symDn n).Amb), hm⟩
    rw [hL, hsym]
    rw [show symA γ (QuotientGroup.mk m)
        = QuotientGroup.mk ((FFModel.symDn_isActionModel n).actSec γ m) from rfl]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
