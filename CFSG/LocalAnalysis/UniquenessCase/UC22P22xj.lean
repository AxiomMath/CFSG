module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xi
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI Matrix Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Matrix

namespace P22x

section Core

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.faithful_modC (d : NatDec ρ Nbar Nb) {g : X} (hg : g ∈ Nbar)
    (h : ∀ i, ∀ y ∈ natIi ρ Nbar (Nb i), ρ g y - y ∈ natC ρ Nbar) : g = 1 := by
  obtain ⟨f, rfl⟩ := d.exists_natPi hg
  have hf : f = 1 := by
    funext i
    obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
    have hφ : φ (f i) = 1 := by
      apply sl2_eq_one_of_fix
      intro y'
      obtain ⟨y, hy, rfl⟩ := hψs y'
      have h1 : ρ ((f i : ↥(Nb i)) : X) y - y ∈ natC ρ Nbar := by
        rw [← d.pi_act f i hy]
        exact h i y hy
      have h2 : ρ ((f i : ↥(Nb i)) : X) y - y ∈ natIi ρ Nbar (Nb i) :=
        (natIi ρ Nbar (Nb i)).sub_mem (d.inv_Ii (d.le i (f i).2) i y hy) hy
      have h3 := hψB _ ⟨h2, h1⟩
      rw [map_sub, hψφ (f i) y hy] at h3
      exact sub_eq_zero.1 h3
    have := φ.injective (hφ.trans (map_one φ).symm)
    simpa using this
  rw [hf, map_one]

theorem NatDec.irr (d : NatDec ρ Nbar Nb) (i : Fin m) {Y : Submodule (ZMod 2) V}
    (hC : natC ρ Nbar ≤ Y) (hY : ∀ h ∈ Nb i, ∀ v ∈ Y, ρ h v ∈ Y) {y : V}
    (hyI : y ∈ natIi ρ Nbar (Nb i)) (hyY : y ∈ Y) (hyC : y ∉ natC ρ Nbar) :
    natIi ρ Nbar (Nb i) ≤ Y := by
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  let U' : AddSubgroup (Fin 2 → F) := (Y ⊓ natIi ρ Nbar (Nb i)).toAddSubgroup.map ψ
  have hU' : ∀ a b : Fin 2, a ≠ b → ∀ c : F, ∀ u ∈ U',
      Matrix.transvection a b c *ᵥ u ∈ U' := by
    intro a b hab c u hu
    obtain ⟨x, hx, rfl⟩ := hu
    set h : ↥(Nb i) := φ.symm (sl2Transvection a b hab c) with hh
    have hmem : ρ (h : X) x ∈ (Y ⊓ natIi ρ Nbar (Nb i)) :=
      ⟨hY h h.2 x hx.1, d.inv_Ii (d.le i h.2) i x hx.2⟩
    refine ⟨ρ (h : X) x, hmem, ?_⟩
    rw [hψφ h x hx.2, hh, MulEquiv.apply_symm_apply, sl2Transvection_mulVec,
      CFSG.Quasithin.H.transvection_mulVec]
  rcases CFSG.Quasithin.H.eq_bot_or_eq_top_of_transvection_inv (d := 2) le_rfl U' hU' with hbot | htop
  · exfalso
    have h1 : ψ y ∈ U' := ⟨y, ⟨hyY, hyI⟩, rfl⟩
    rw [hbot] at h1
    have h0 : ψ y = 0 := h1
    exact hyC (hψA y hyI h0).2
  · intro z hz
    have h1 : ψ z ∈ U' := by rw [htop]; trivial
    obtain ⟨x, hx, hxz⟩ := h1
    have h2 : z - x ∈ natIi ρ Nbar (Nb i) := (natIi ρ Nbar (Nb i)).sub_mem hz hx.2
    have h3 : ψ (z - x) = 0 := by rw [map_sub, hxz, sub_self]
    have h4 := (hψA _ h2 h3).2
    have h5 := Y.add_mem hx.1 (hC h4)
    simpa using h5

theorem natI_inv_of_normalizer {t : X} (ht : t ∈ normalizer (Nbar : Set X)) :
    ∀ v ∈ natI ρ Nbar, ρ t v ∈ natI ρ Nbar :=
  commOn_invariant (A := Nbar) (U := ⊤) (g := t) (fun a ha => (Subgroup.mem_normalizer_iff.1 ht a).1 ha)
    (fun u _ => trivial)

theorem natC_inv_of_normalizer {t : X} (ht : t ∈ normalizer (Nbar : Set X)) :
    ∀ c ∈ natC ρ Nbar, ρ t c ∈ natC ρ Nbar := by
  intro c hc
  refine ⟨natI_inv_of_normalizer ht c hc.1, fun a ha => ?_⟩
  have hta : t⁻¹ * a * t ∈ Nbar := by
    have := (Subgroup.mem_normalizer_iff.1 ht (t⁻¹ * a * t)).1
    exact (Subgroup.mem_normalizer_iff.1 ht (t⁻¹ * a * t)).2 (by simpa [mul_assoc] using ha)
  have h1 : ρ a (ρ t c) = ρ t (ρ (t⁻¹ * a * t) c) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [h1, hc.2 _ hta]

theorem rho_conj_apply (t g : X) (v : V) : ρ t (ρ g v) = ρ (t * g * t⁻¹) (ρ t v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem NatDec.act_trivial_modC [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) (i : Fin m)
    {Q : Subgroup X} (hQN : Q ≤ Nbar) (hQ2 : IsPGroup 2 Q)
    (himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w)
    {t : X} (ht : t ∈ normalizer (Nbar : Set X))
    (hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t v = v)
    {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Nat.card ↥(Nb i)) {k : ℕ} (hk : t ^ (p ^ k) = 1) :
    ∀ y ∈ natIi ρ Nbar (Nb i), ρ t y - y ∈ natC ρ Nbar := by
  classical
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  set A := natIi ρ Nbar (Nb i) with hA
  set C := natC ρ Nbar with hCdef
  have htinv : t⁻¹ ∈ normalizer (Nbar : Set X) := inv_mem ht
  have hCt : ∀ c ∈ C, ρ t c ∈ C := natC_inv_of_normalizer ht
  have hCt' : ∀ c ∈ C, ρ t⁻¹ c ∈ C := natC_inv_of_normalizer htinv
  have hAI : A ≤ natI ρ Nbar := d.Ii_le_I i
  set P := d.proj i Q with hP
  have hPle : P ≤ Nb i := d.proj_le i Q
  have hP2 : IsPGroup 2 P := d.isPGroup_proj i hQ2
  set Q' : Subgroup ↥(StatedSL 2 F) := (P.subgroupOf (Nb i)).map φ.toMonoidHom with hQ'def
  have hQ'2 : IsPGroup 2 Q' := (hP2.comap_subtype).map _
  have hrel : ∀ y ∈ A, (∀ a ∈ Q, ρ a y - y ∈ C) ↔ ψ y ∈ sl2Fix Q' := by
    intro y hy
    constructor
    · intro hQy g hg
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨a, haQ, hab⟩ := d.exists_act_of_proj i (show (b : X) ∈ P from hb) hy
      have h1 : ρ (b : X) y - y ∈ C := by rw [← hab]; exact hQy a haQ
      have h2 : ρ (b : X) y - y ∈ A := A.sub_mem (d.inv_Ii (d.le i b.2) i y hy) hy
      have h3 := hψB _ ⟨h2, h1⟩
      rw [map_sub, hψφ b y hy] at h3
      exact sub_eq_zero.1 h3
    · intro hy' a ha
      obtain ⟨b, hb, hab⟩ := d.exists_proj_act i hQN ha hy
      have hbP : (⟨b, hPle hb⟩ : ↥(Nb i)) ∈ P.subgroupOf (Nb i) := hb
      have h1 := hy' (φ ⟨b, hPle hb⟩) (Subgroup.mem_map_of_mem _ hbP)
      have h2 : ρ b y - y ∈ A := A.sub_mem (d.inv_Ii (d.le i (hPle hb)) i y hy) hy
      have h3 : ψ (ρ b y - y) = 0 := by
        have := hψφ ⟨b, hPle hb⟩ y hy
        rw [map_sub]
        exact sub_eq_zero.2 (this.trans h1)
      rw [hab]
      exact (hψA _ h2 h3).2
  have hfixvec : ∀ y ∈ A, ψ y ∈ sl2Fix Q' → ρ t y = y := by
    intro y hy hy'
    have hmod := (hrel y hy).2 hy'
    have hfa := himg y (hAI hy) hmod
    exact hfix y ⟨hAI hy, fun a ha => hfa a ha⟩
  obtain ⟨w₀, hw₀, hw₀fix⟩ := exists_ne_zero_mem_sl2Fix hF hn Q' hQ'2
  choose lift hliftA hliftψ using hψs
  have hψ0 : ∀ a ∈ A, ψ a = 0 ↔ a ∈ C := fun a ha =>
    ⟨fun h => (hψA a ha h).2, fun h => hψB a ⟨ha, h⟩⟩
  have hAC_inv : ∀ g ∈ Nbar, ∀ v ∈ A ⊔ C, ρ g v ∈ A ⊔ C := by
    intro g hg v hv
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, natC_fix hg hc]
    exact Submodule.add_mem_sup (d.inv_Ii hg i a ha) hc
  have hy₀fix : ρ t (lift w₀) = lift w₀ :=
    hfixvec _ (hliftA w₀) (by rw [hliftψ]; exact hw₀fix)
  have hy₀C : lift w₀ ∉ C := by
    intro hcon
    exact hw₀ (by rw [← hliftψ w₀]; exact (hψ0 _ (hliftA w₀)).2 hcon)
  let Y : Submodule (ZMod 2) V := (A ⊔ C).comap (ρ t)
  have hYC : C ≤ Y := fun c hc => Submodule.mem_comap.2 (Submodule.mem_sup_right (hCt c hc))
  have hYinv : ∀ h ∈ Nb i, ∀ v ∈ Y, ρ h v ∈ Y := by
    intro h hh v hv
    refine Submodule.mem_comap.2 ?_
    rw [rho_conj_apply]
    exact hAC_inv _ ((Subgroup.mem_normalizer_iff.1 ht h).1 (d.le i hh)) _ (Submodule.mem_comap.1 hv)
  have hy₀Y : lift w₀ ∈ Y := by
    refine Submodule.mem_comap.2 ?_
    rw [hy₀fix]
    exact Submodule.mem_sup_left (hliftA w₀)
  have hAY : A ≤ Y := d.irr i hYC hYinv (hliftA w₀) hy₀Y hy₀C
  have hdec : ∀ y ∈ A, ∃ a ∈ A, ρ t y - a ∈ C := by
    intro y hy
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (Submodule.mem_comap.1 (hAY hy))
    exact ⟨a, ha, by rw [← hac, add_sub_cancel_left]; exact hc⟩
  choose! dec hdecA hdecC using hdec
  have K1 : ∀ y ∈ A, ∀ z ∈ A, y - z ∈ C → ψ (dec y) = ψ (dec z) := by
    intro y hy z hz hyz
    have hmem : dec y - dec z ∈ C := by
      have h1 := C.add_mem (C.sub_mem (hCt _ hyz) (hdecC y hy)) (hdecC z hz)
      have e : ρ t (y - z) - (ρ t y - dec y) + (ρ t z - dec z) = dec y - dec z := by
        rw [map_sub]; abel
      rwa [e] at h1
    have := (hψ0 _ (A.sub_mem (hdecA y hy) (hdecA z hz))).2 hmem
    rwa [map_sub, sub_eq_zero] at this
  have K2 : ∀ y ∈ A, ∀ z ∈ A, ψ (dec (y + z)) = ψ (dec y) + ψ (dec z) := by
    intro y hy z hz
    have hyz := A.add_mem hy hz
    have hmem : dec (y + z) - (dec y + dec z) ∈ C := by
      have h1 := C.add_mem (C.add_mem (C.neg_mem (hdecC (y + z) hyz)) (hdecC y hy)) (hdecC z hz)
      have e : -(ρ t (y + z) - dec (y + z)) + (ρ t y - dec y) + (ρ t z - dec z) =
          dec (y + z) - (dec y + dec z) := by
        rw [map_add]; abel
      rwa [e] at h1
    have := (hψ0 _ (A.sub_mem (hdecA _ hyz) (A.add_mem (hdecA y hy) (hdecA z hz)))).2 hmem
    rwa [map_sub, map_add, sub_eq_zero] at this
  obtain ⟨Θf, hΘf⟩ : ∃ Θf : (Fin 2 → F) → (Fin 2 → F), ∀ y ∈ A, Θf (ψ y) = ψ (dec y) := by
    refine ⟨fun v => ψ (dec (lift v)), fun y hy => ?_⟩
    have hz := hliftA (ψ y)
    refine K1 _ hz y hy ((hψ0 _ (A.sub_mem hz hy)).1 ?_)
    rw [map_sub, hliftψ, sub_self]
  have Θadd : ∀ v w, Θf (v + w) = Θf v + Θf w := by
    intro v w
    have hv := hΘf (lift v) (hliftA v)
    have hw := hΘf (lift w) (hliftA w)
    rw [hliftψ] at hv hw
    have h1 : v + w = ψ (lift v + lift w) := by rw [map_add, hliftψ, hliftψ]
    rw [h1, hΘf _ (A.add_mem (hliftA v) (hliftA w)), hv, hw]
    exact K2 _ (hliftA v) _ (hliftA w)
  let Θ0 : (Fin 2 → F) →+ (Fin 2 → F) := AddMonoidHom.mk' Θf Θadd
  have Θinj : Function.Injective Θ0 := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : Θf v = 0 := hv
    have hy := hliftA v
    have h1 := hΘf (lift v) hy
    rw [hliftψ, hv'] at h1
    have hdecC' : dec (lift v) ∈ C := (hψ0 _ (hdecA _ hy)).1 h1.symm
    have hρC : ρ t (lift v) ∈ C := by
      have := C.add_mem (hdecC _ hy) hdecC'
      rwa [sub_add_cancel] at this
    have hyC : lift v ∈ C := by
      have := hCt' _ hρC
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    rw [← hliftψ v]
    exact (hψ0 _ hy).2 hyC
  let Θ : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    AddEquiv.ofBijective Θ0 (Finite.injective_iff_bijective.1 Θinj)
  have hΘapp : ∀ v, Θ v = Θf v := fun v => rfl
  have hΘ : ∀ g : ↥(StatedSL 2 F), ∃ g' : ↥(StatedSL 2 F), ∀ v,
      Θ ((((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ v := by
    intro g
    obtain ⟨h, hφh⟩ : ∃ h : ↥(Nb i), φ h = g := ⟨φ.symm g, φ.apply_symm_apply g⟩
    have hh' : t * (h : X) * t⁻¹ ∈ Nbar :=
      (Subgroup.mem_normalizer_iff.1 ht (h : X)).1 (d.le i h.2)
    obtain ⟨f, hf⟩ := d.exists_natPi hh'
    refine ⟨φ (f i), fun v => ?_⟩
    have hy := hliftA v
    have hψy := hliftψ v
    have hyh : ρ (h : X) (lift v) ∈ A := d.inv_Ii (d.le i h.2) i _ hy
    have hz1 : dec (lift v) ∈ A := hdecA _ hy
    have hz2 : ρ ((f i : ↥(Nb i)) : X) (dec (lift v)) ∈ A := d.inv_Ii (d.le i (f i).2) i _ hz1
    have e1 : ρ t (ρ (h : X) (lift v)) =
        ρ ((f i : ↥(Nb i)) : X) (dec (lift v)) + (ρ t (lift v) - dec (lift v)) := by
      have hc1 := hdecC _ hy
      calc ρ t (ρ (h : X) (lift v)) = ρ (t * (h : X) * t⁻¹) (ρ t (lift v)) := rho_conj_apply _ _ _
        _ = ρ (d.natPi f) (dec (lift v) + (ρ t (lift v) - dec (lift v))) := by
          rw [← hf, add_sub_cancel]
        _ = ρ (d.natPi f) (dec (lift v)) + ρ (d.natPi f) (ρ t (lift v) - dec (lift v)) :=
          map_add _ _ _
        _ = _ := by rw [d.pi_act f i hz1, natC_fix (d.natPi_mem f) hc1]
    have e2 : ψ (dec (ρ (h : X) (lift v))) = ψ (ρ ((f i : ↥(Nb i)) : X) (dec (lift v))) := by
      have hmem : dec (ρ (h : X) (lift v)) - ρ ((f i : ↥(Nb i)) : X) (dec (lift v)) ∈ C := by
        have h1 := C.sub_mem (hdecC _ hy) (hdecC _ hyh)
        have e : (ρ t (lift v) - dec (lift v)) -
            (ρ t (ρ (h : X) (lift v)) - dec (ρ (h : X) (lift v))) =
            dec (ρ (h : X) (lift v)) - ρ ((f i : ↥(Nb i)) : X) (dec (lift v)) := by
          rw [e1]; abel
        rwa [e] at h1
      have := (hψ0 _ (A.sub_mem (hdecA _ hyh) hz2)).2 hmem
      rwa [map_sub, sub_eq_zero] at this
    have h3 : ψ (ρ (h : X) (lift v)) =
        (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
      rw [hψφ h _ hy, hφh, hψy]
    rw [hΘapp, ← h3, hΘf _ hyh, e2, hψφ (f i) _ hz1, ← hΘf _ hy, hψy, hΘapp]
  have hfixΘ : ∀ c : F, Θ (c • w₀) = c • w₀ := by
    intro c
    have hy := hliftA (c • w₀)
    have hψy := hliftψ (c • w₀)
    have hcfix : c • w₀ ∈ sl2Fix Q' := Submodule.smul_mem _ c hw₀fix
    have hρ : ρ t (lift (c • w₀)) = lift (c • w₀) := hfixvec _ hy (by rw [hψy]; exact hcfix)
    have h1 := hΘf _ hy
    rw [hψy] at h1
    rw [hΘapp, h1]
    have hmem : lift (c • w₀) - dec (lift (c • w₀)) ∈ C := by
      have := hdecC _ hy
      rwa [hρ] at this
    have h2 := (hψ0 _ (A.sub_mem hy (hdecA _ hy))).2 hmem
    rw [map_sub, sub_eq_zero] at h2
    rw [← h2, hψy]
  have hiter : ∀ n : ℕ, ∀ y ∈ A, dec^[n] y ∈ A ∧ ρ (t ^ n) y - dec^[n] y ∈ C := by
    intro n
    induction n with
    | zero =>
      intro y hy
      refine ⟨hy, ?_⟩
      simp
    | succ n ih =>
      intro y hy
      obtain ⟨hz, hc⟩ := ih y hy
      rw [Function.iterate_succ_apply']
      refine ⟨hdecA _ hz, ?_⟩
      have e : ρ (t ^ (n + 1)) y - dec (dec^[n] y) =
          (ρ t (dec^[n] y) - dec (dec^[n] y)) + ρ t (ρ (t ^ n) y - dec^[n] y) := by
        rw [pow_succ', map_mul, Module.End.mul_apply, map_sub]; abel
      rw [e]
      exact C.add_mem (hdecC _ hz) (hCt _ hc)
  have hΘiter : ∀ n : ℕ, ∀ y ∈ A, (⇑Θ)^[n] (ψ y) = ψ (dec^[n] y) := by
    intro n
    induction n with
    | zero => intro y hy; rfl
    | succ n ih =>
      intro y hy
      rw [Function.iterate_succ_apply', ih y hy, hΘapp, hΘf _ (hiter n y hy).1,
        Function.iterate_succ_apply']
  have hord : ∃ k' : ℕ, ∀ v, (⇑Θ)^[p ^ k'] v = v := by
    refine ⟨k, fun v => ?_⟩
    have h1 := hΘiter (p ^ k) (lift v) (hliftA v)
    rw [hliftψ] at h1
    rw [h1]
    have h2 := (hiter (p ^ k) (lift v) (hliftA v)).2
    rw [hk, map_one, Module.End.one_apply] at h2
    have h3 := (hψ0 _ (A.sub_mem (hliftA v) (hiter (p ^ k) (lift v) (hliftA v)).1)).2 h2
    rw [map_sub, sub_eq_zero, hliftψ] at h3
    exact h3.symm
  have hpF' : ¬ p ∣ Nat.card ↥(StatedSL 2 F) := by
    rwa [← Nat.card_congr φ.toEquiv]
  have hid := sl2_theta_eq_id hp hpF' Θ hΘ hw₀ hfixΘ hord
  intro y hy
  have h1 : ψ (dec y) = ψ y := by
    have := hid (ψ y)
    rwa [hΘapp, hΘf _ hy] at this
  have h2 : y - dec y ∈ C :=
    (hψ0 _ (A.sub_mem hy (hdecA y hy))).1 (by rw [map_sub, h1, sub_self])
  have h3 := C.sub_mem (hdecC y hy) h2
  have e : ρ t y - dec y - (y - dec y) = ρ t y - y := by abel
  rwa [e] at h3

theorem NatDec.commute_of_fixed [Finite V] [Finite X] (d : NatDec ρ Nbar Nb)
    {Q : Subgroup X} (hQN : Q ≤ Nbar) (hQ2 : IsPGroup 2 Q)
    (himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w)
    {t : X} (ht : t ∈ normalizer (Nbar : Set X))
    (hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t v = v)
    {p : ℕ} (hp : p.Prime) (hpF : ∀ i, ¬ p ∣ Nat.card ↥(Nb i)) {k : ℕ} (hk : t ^ (p ^ k) = 1) :
    ∀ g ∈ Nbar, t * g = g * t := by
  intro g hg
  have htinv : t⁻¹ ∈ normalizer (Nbar : Set X) := inv_mem ht
  have hfix' : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t⁻¹ v = v := by
    intro v hv
    calc ρ t⁻¹ v = ρ t⁻¹ (ρ t v) := by rw [hfix v hv]
      _ = v := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hk' : t⁻¹ ^ (p ^ k) = 1 := by rw [inv_pow, hk, inv_one]
  have h1 := fun i => d.act_trivial_modC i hQN hQ2 himg ht hfix hp (hpF i) hk
  have h2 := fun i => d.act_trivial_modC i hQN hQ2 himg htinv hfix' hp (hpF i) hk'
  have hCt := natC_inv_of_normalizer (ρ := ρ) ht
  have hs : t * g * t⁻¹ * g⁻¹ = 1 := by
    have hgmem : t * g * t⁻¹ * g⁻¹ ∈ Nbar :=
      Nbar.mul_mem ((Subgroup.mem_normalizer_iff.1 ht g).1 hg) (Nbar.inv_mem hg)
    refine d.faithful_modC hgmem fun i y hy => ?_
    have hy1 : ρ g⁻¹ y ∈ natIi ρ Nbar (Nb i) := d.inv_Ii (Nbar.inv_mem hg) i y hy
    have c1 := h2 i _ hy1
    have c2 := h1 i y hy
    have hρs : ρ (t * g * t⁻¹ * g⁻¹) y = ρ t (ρ g (ρ t⁻¹ (ρ g⁻¹ y))) := by
      simp only [map_mul, Module.End.mul_apply]
    have hgy₁ : ρ g (ρ g⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨c₁, hc₁, hc₁eq⟩ : ∃ c₁ ∈ natC ρ Nbar, ρ t⁻¹ (ρ g⁻¹ y) = ρ g⁻¹ y + c₁ :=
      ⟨ρ t⁻¹ (ρ g⁻¹ y) - ρ g⁻¹ y, c1, by abel⟩
    have key : ρ (t * g * t⁻¹ * g⁻¹) y = y + (ρ t y - y) + ρ t c₁ := by
      rw [hρs, hc₁eq, map_add, hgy₁, natC_fix hg hc₁, map_add]; abel
    have e : ρ (t * g * t⁻¹ * g⁻¹) y - y = (ρ t y - y) + ρ t c₁ := by
      rw [key]; abel
    rw [e]
    exact (natC ρ Nbar).add_mem c2 (hCt c₁ hc₁)
  have h3 : t * g * t⁻¹ = g := mul_inv_eq_one.1 hs
  exact mul_inv_eq_iff_eq_mul.1 h3

end Core

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
