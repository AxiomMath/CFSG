module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xl
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI Matrix Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Matrix

namespace P22x

section Core25

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.fixed_mod_of_sl2Fix (d : NatDec ρ Nbar Nb) (i : Fin m) {F : Type} [Field F] [Finite F]
    (φ : ↥(Nb i) ≃* ↥(StatedSL 2 F)) (ψ : V →+ (Fin 2 → F))
    (hψA : ∀ x ∈ natIi ρ Nbar (Nb i), ψ x = 0 → x ∈ natIi ρ Nbar (Nb i) ⊓ natC ρ Nbar)
    (hψφ : ∀ (h : ↥(Nb i)) (x : V), x ∈ natIi ρ Nbar (Nb i) →
      ψ (ρ (h : X) x) = ((((φ h : ↥(StatedSL 2 F)) : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ ψ x)
    {Q : Subgroup X} (hQN : Q ≤ Nbar) {y : V} (hy : y ∈ natIi ρ Nbar (Nb i))
    (hy' : ψ y ∈ sl2Fix (((d.proj i Q).subgroupOf (Nb i)).map φ.toMonoidHom)) :
    ∀ a ∈ Q, ρ a y - y ∈ natC ρ Nbar := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := d.exists_proj_act i hQN ha hy
  have hPle : d.proj i Q ≤ Nb i := d.proj_le i Q
  have hbP : (⟨b, hPle hb⟩ : ↥(Nb i)) ∈ (d.proj i Q).subgroupOf (Nb i) := hb
  have h1 := hy' (φ ⟨b, hPle hb⟩) (Subgroup.mem_map_of_mem _ hbP)
  have h2 : ρ b y - y ∈ natIi ρ Nbar (Nb i) :=
    (natIi ρ Nbar (Nb i)).sub_mem (d.inv_Ii (d.le i (hPle hb)) i y hy) hy
  have h3 : ψ (ρ b y - y) = 0 := by
    have := hψφ ⟨b, hPle hb⟩ y hy
    rw [map_sub]
    exact sub_eq_zero.2 (this.trans h1)
  rw [hab]
  exact (hψA _ h2 h3).2

theorem NatDec.maps_Ii [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) (i : Fin m)
    {Q : Subgroup X} (hQN : Q ≤ Nbar) (hQ2 : IsPGroup 2 Q)
    (himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w)
    {t : X} (ht : t ∈ normalizer (Nbar : Set X))
    (hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t v = v) :
    ∀ y ∈ natIi ρ Nbar (Nb i), ρ t y ∈ natIi ρ Nbar (Nb i) ⊔ natC ρ Nbar := by
  classical
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  set A := natIi ρ Nbar (Nb i) with hA
  set C := natC ρ Nbar with hCdef
  have hCt : ∀ c ∈ C, ρ t c ∈ C := natC_inv_of_normalizer ht
  have hAI : A ≤ natI ρ Nbar := d.Ii_le_I i
  set P := d.proj i Q with hP
  have hP2 : IsPGroup 2 P := d.isPGroup_proj i hQ2
  set Q' : Subgroup ↥(StatedSL 2 F) := (P.subgroupOf (Nb i)).map φ.toMonoidHom with hQ'def
  have hQ'2 : IsPGroup 2 Q' := (hP2.comap_subtype).map _
  have hψ0 : ∀ a ∈ A, ψ a = 0 ↔ a ∈ C := fun a ha =>
    ⟨fun h => (hψA a ha h).2, fun h => hψB a ⟨ha, h⟩⟩
  obtain ⟨w₀, hw₀, hw₀fix⟩ := exists_ne_zero_mem_sl2Fix hF hn Q' hQ'2
  choose lift hliftA hliftψ using hψs
  have hAC_inv : ∀ g ∈ Nbar, ∀ v ∈ A ⊔ C, ρ g v ∈ A ⊔ C := by
    intro g hg v hv
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, natC_fix hg hc]
    exact Submodule.add_mem_sup (d.inv_Ii hg i a ha) hc
  have hy₀mod := d.fixed_mod_of_sl2Fix i φ ψ hψA hψφ hQN (hliftA w₀)
    (by rw [hliftψ]; exact hw₀fix)
  have hy₀fix : ρ t (lift w₀) = lift w₀ :=
    hfix _ ⟨hAI (hliftA w₀), fun a ha => himg _ (hAI (hliftA w₀)) hy₀mod a ha⟩
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
  exact fun y hy => Submodule.mem_comap.1 (hAY hy)

theorem NatDec.conj_mem_factor [Finite V] (d : NatDec ρ Nbar Nb) (i : Fin m) {t : X}
    (ht : t ∈ normalizer (Nbar : Set X))
    (hM : ∀ j, j ≠ i → ∀ y ∈ natIi ρ Nbar (Nb j), ρ t⁻¹ y ∈ natIi ρ Nbar (Nb j) ⊔ natC ρ Nbar)
    {h : X} (hh : h ∈ Nb i) : t * h * t⁻¹ ∈ Nb i := by
  classical
  have hh' : t * h * t⁻¹ ∈ Nbar := (Subgroup.mem_normalizer_iff.1 ht h).1 (d.le i hh)
  obtain ⟨f, hf⟩ := d.exists_natPi hh'
  have hfj : ∀ j, j ≠ i → f j = 1 := by
    intro j hji
    have h1 : ((f j : ↥(Nb j)) : X) = 1 := by
      refine d.faithful j (f j).2 (fun x hx => ?_)
      rw [← d.pi_act f j hx, hf]
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (hM j hji x hx)
      have h2 : ρ h (ρ t⁻¹ x) = ρ t⁻¹ x := by
        rw [← hac, map_add, d.lemma21 (Ne.symm hji) hh ha, natC_fix (d.le i hh) hc]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h2,
        ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    exact Subtype.ext h1
  have hfeq : f = Pi.mulSingle i (f i) := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · rw [Pi.mulSingle_eq_of_ne hji, hfj j hji]
  have h1 : d.natPi f = ((f i : ↥(Nb i)) : X) :=
    (congrArg d.natPi hfeq).trans (d.natPi_mulSingle i (f i))
  rw [← hf, h1]
  exact (f i).2

end Core25

section Arith

variable {F : Type} [Field F] [Finite F]

theorem card_eq_of_odd_index {n : ℕ} (hF : Nat.card F = 2 ^ n) {K : Type} [Group K] [Finite K]
    (φ : K ≃* ↥(StatedSL 2 F)) (P : Subgroup K) (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    Nat.card P = Nat.card F := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have h1 : Nat.card P * P.index = Nat.card K := P.card_mul_index
  have h2 : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, card_statedSL_two]
  have hodd1 : Odd (Nat.card F ^ 2 - 1) := odd_card_sq_sub_one hF
  have hodd2 : Odd P.index := Nat.odd_iff.2 (by omega)
  have hcop1 : Nat.Coprime (2 ^ a) (Nat.card F ^ 2 - 1) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hodd1)
  have hcop2 : Nat.Coprime (Nat.card F) P.index := by
    rw [hF]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd2)
  have hmul : 2 ^ a * P.index = Nat.card F * (Nat.card F ^ 2 - 1) := by rw [← ha, h1, h2]
  have hd1 : 2 ^ a ∣ Nat.card F := hcop1.dvd_of_dvd_mul_right (Dvd.intro _ hmul)
  have hd2 : Nat.card F ∣ 2 ^ a :=
    hcop2.dvd_of_dvd_mul_right (hmul ▸ Dvd.intro _ rfl)
  rw [ha]
  exact Nat.dvd_antisymm hd1 hd2

end Arith

section Core25b

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.exists_proj_of_stab [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) (i : Fin m)
    {Q : Subgroup X} (hQN : Q ≤ Nbar) (hQ2 : IsPGroup 2 Q)
    (hQi : ¬ 2 ∣ (d.proj i Q).relIndex (Nb i))
    (himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w)
    {t : X} (ht : t ∈ normalizer (Nbar : Set X))
    (hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t v = v) {k : ℕ} (hk : t ^ (2 ^ k) = 1) :
    ∃ q ∈ d.proj i Q, ∀ y ∈ natIi ρ Nbar (Nb i), ρ t y - ρ q y ∈ natC ρ Nbar := by
  classical
  have hAY := d.maps_Ii i hQN hQ2 himg ht hfix
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
  have hψ0 : ∀ a ∈ A, ψ a = 0 ↔ a ∈ C := fun a ha =>
    ⟨fun h => (hψA a ha h).2, fun h => hψB a ⟨ha, h⟩⟩
  have hfixvec : ∀ y ∈ A, ψ y ∈ sl2Fix Q' → ρ t y = y := fun y hy hy' =>
    hfix y ⟨hAI hy, fun a ha =>
      himg y (hAI hy) (d.fixed_mod_of_sl2Fix i φ ψ hψA hψφ hQN hy hy') a ha⟩
  obtain ⟨w₀, hw₀, hw₀fix⟩ := exists_ne_zero_mem_sl2Fix hF hn Q' hQ'2
  choose lift hliftA hliftψ using hψs
  have hcard : Nat.card Q' = Nat.card F := by
    have h1 : Nat.card Q' = Nat.card (P.subgroupOf (Nb i)) :=
      Subgroup.card_map_of_injective φ.injective
    have h2 : IsPGroup 2 (P.subgroupOf (Nb i)) := hP2.comap_subtype
    rw [h1]
    exact card_eq_of_odd_index hF φ _ h2 hQi
  have hdec : ∀ y ∈ A, ∃ a ∈ A, ρ t y - a ∈ C := by
    intro y hy
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (hAY y hy)
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
  have hord : ∀ v, (⇑Θ)^[2 ^ k] v = v := by
    intro v
    have h1 := hΘiter (2 ^ k) (lift v) (hliftA v)
    rw [hliftψ] at h1
    rw [h1]
    have h2 := (hiter (2 ^ k) (lift v) (hliftA v)).2
    rw [hk, map_one, Module.End.one_apply] at h2
    have h3 := (hψ0 _ (A.sub_mem (hliftA v) (hiter (2 ^ k) (lift v) (hliftA v)).1)).2 h2
    rw [map_sub, sub_eq_zero, hliftψ] at h3
    exact h3.symm
  obtain ⟨g, hgQ, hg⟩ := sl2_theta_mem hF hn Q' hcard hw₀ hw₀fix Θ hΘ hfixΘ hord
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hgQ
  have hbP : (b : X) ∈ P := hb
  refine ⟨(b : X), hbP, fun y hy => ?_⟩
  have h1 : ψ (dec y) = ψ (ρ (b : X) y) := by
    have hgy := hg (ψ y)
    rw [hψφ b y hy, ← hΘf _ hy, ← hΘapp]
    exact hgy
  have h2 : dec y - ρ (b : X) y ∈ C :=
    (hψ0 _ (A.sub_mem (hdecA y hy) (d.inv_Ii (d.le i b.2) i y hy))).1 (by rw [map_sub, h1, sub_self])
  have h3 := C.add_mem (hdecC y hy) h2
  have e : ρ t y - dec y + (dec y - ρ (b : X) y) = ρ t y - ρ (b : X) y := by abel
  rwa [e] at h3

theorem NatDec.step67 [Finite V] (d : NatDec ρ Nbar Nb) (i : Fin m) {t' : X}
    (ht' : t' ∈ normalizer (Nbar : Set X))
    (hM : ∀ j, ∀ y ∈ natIi ρ Nbar (Nb j), ρ t' y ∈ natIi ρ Nbar (Nb j) ⊔ natC ρ Nbar)
    (hM' : ∀ j, ∀ y ∈ natIi ρ Nbar (Nb j), ρ t'⁻¹ y ∈ natIi ρ Nbar (Nb j) ⊔ natC ρ Nbar)
    (hi : ∀ y ∈ natIi ρ Nbar (Nb i), ρ t' y - y ∈ natC ρ Nbar) :
    (∀ g ∈ Nb i, t' * g = g * t') ∧ ∀ y ∈ natIi ρ Nbar (Nb i), ρ t' y = y := by
  classical
  set C := natC ρ Nbar with hCdef
  have hCt : ∀ c ∈ C, ρ t' c ∈ C := natC_inv_of_normalizer ht'
  have hinv : ∀ y, ρ t' (ρ t'⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hi' : ∀ y ∈ natIi ρ Nbar (Nb i), ρ t'⁻¹ y - y ∈ C := by
    intro y hy
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (hM' i y hy)
    have h1 : y = ρ t' a + ρ t' c := by
      have := hinv y
      rw [← hac, map_add] at this
      exact this.symm
    have e : ρ t'⁻¹ y - y = -(ρ t' a - a) - (ρ t' c - c) := by
      have e1 : ρ t'⁻¹ y - y = (a + c) - (ρ t' a + ρ t' c) := by rw [hac, ← h1]
      rw [e1]; abel
    rw [e]
    exact C.sub_mem (C.neg_mem (hi a ha)) (C.sub_mem (hCt c hc) hc)
  have hfixIC : ∀ j, j ≠ i → ∀ n ∈ Nb i, ∀ z ∈ natIi ρ Nbar (Nb j) ⊔ C, ρ n z = z := by
    intro j hji n hn z hz
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add, d.lemma21 (Ne.symm hji) hn ha, natC_fix (d.le i hn) hc]
  have hcomm : ∀ g ∈ Nb i, t' * g * t'⁻¹ * g⁻¹ = 1 := by
    intro g hg
    have hgN : g ∈ Nbar := d.le i hg
    have hcN : t' * g * t'⁻¹ * g⁻¹ ∈ Nbar :=
      Nbar.mul_mem ((Subgroup.mem_normalizer_iff.1 ht' g).1 hgN) (Nbar.inv_mem hgN)
    refine d.faithful_modC hcN fun j y hy => ?_
    have hρs : ρ (t' * g * t'⁻¹ * g⁻¹) y = ρ t' (ρ g (ρ t'⁻¹ (ρ g⁻¹ y))) := by
      simp only [map_mul, Module.End.mul_apply]
    by_cases hji : j = i
    · subst hji
      have hy1 : ρ g⁻¹ y ∈ natIi ρ Nbar (Nb j) := d.inv_Ii (Nbar.inv_mem hgN) j y hy
      have hgy₁ : ρ g (ρ g⁻¹ y) = y := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      obtain ⟨c₁, hc₁, hc₁eq⟩ : ∃ c₁ ∈ C, ρ t'⁻¹ (ρ g⁻¹ y) = ρ g⁻¹ y + c₁ :=
        ⟨_, hi' _ hy1, by abel⟩
      have key : ρ (t' * g * t'⁻¹ * g⁻¹) y = y + (ρ t' y - y) + ρ t' c₁ := by
        rw [hρs, hc₁eq, map_add, hgy₁, natC_fix hgN hc₁, map_add]; abel
      have e : ρ (t' * g * t'⁻¹ * g⁻¹) y - y = (ρ t' y - y) + ρ t' c₁ := by
        rw [key]; abel
      rw [e]
      exact C.add_mem (hi y hy) (hCt c₁ hc₁)
    · have hg1 : ρ g⁻¹ y = y := d.lemma21 (Ne.symm hji) (inv_mem hg) hy
      have h2 : ρ g (ρ t'⁻¹ y) = ρ t'⁻¹ y := by
        obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (hM' j y hy)
        rw [← hac, map_add, d.lemma21 (Ne.symm hji) hg ha, natC_fix hgN hc]
      have h3 : ρ (t' * g * t'⁻¹ * g⁻¹) y = y := by
        rw [hρs, hg1, h2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply]
      rw [h3, sub_self]
      exact C.zero_mem
  have hcommute : ∀ g ∈ Nb i, t' * g = g * t' := fun g hg =>
    mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 (hcomm g hg))
  refine ⟨hcommute, ?_⟩
  have hW : ∀ n ∈ Nb i, ∀ x ∈ natI ρ Nbar, ρ n (ρ t' x - x) = ρ t' x - x := by
    intro n hn x hx
    let W : Submodule (ZMod 2) V :=
      LinearMap.ker ((ρ n - LinearMap.id) ∘ₗ (ρ t' - LinearMap.id))
    have hWmem : ∀ x, x ∈ W ↔ ρ n (ρ t' x - x) = ρ t' x - x := by
      intro x
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.id_apply]
      exact sub_eq_zero
    have hle : natI ρ Nbar ≤ W := by
      rw [← d.sum.1]
      refine sup_le (iSup_le fun j => fun x hx => ?_) (fun x hx => ?_)
      · have hx' : x ∈ natIi ρ Nbar (Nb j) := hx
        rw [hWmem]
        by_cases hji : j = i
        · subst hji
          exact natC_fix (d.le j hn) (hi x hx')
        · exact hfixIC j hji n hn _
            ((natIi ρ Nbar (Nb j) ⊔ C).sub_mem (hM j x hx') (Submodule.mem_sup_left hx'))
      · rw [hWmem]
        exact natC_fix (d.le i hn) (C.sub_mem (hCt x hx) hx)
    exact (hWmem x).1 (hle hx)
  intro y hy
  have hle : natIi ρ Nbar (Nb i) ≤ LinearMap.ker (ρ t' - LinearMap.id) := by
    rw [natIi, commOn_le_iff]
    intro n hn x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    have h1 : ρ t' (ρ n x) = ρ n (ρ t' x) := by
      rw [← Module.End.mul_apply, ← map_mul, hcommute n hn, map_mul, Module.End.mul_apply]
    rw [map_sub, h1]
    have := hW n hn x hx
    rw [map_sub] at this
    calc ρ n (ρ t' x) - ρ t' x - (ρ n x - x)
        = (ρ n (ρ t' x) - ρ n x) - (ρ t' x - x) := by abel
      _ = 0 := by rw [this, sub_self]
  have := hle hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at this
  exact sub_eq_zero.1 this

theorem NatDec.lemma25 [Finite V] [Finite X] (d : NatDec ρ Nbar Nb) (i : Fin m)
    {Q : Subgroup X} (hQN : Q ≤ Nbar) (hQ2 : IsPGroup 2 Q)
    (hQi : ¬ 2 ∣ (d.proj i Q).relIndex (Nb i))
    (himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w)
    {t : X} (ht : t ∈ normalizer (Nbar : Set X))
    (hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t v = v) {k : ℕ} (hk : t ^ (2 ^ k) = 1) :
    (∀ h ∈ Nb i, t * h * t⁻¹ ∈ Nb i) ∧
      ∃ q ∈ d.proj i Q, (∀ y ∈ natIi ρ Nbar (Nb i), ρ t y = ρ q y) ∧
        ∀ g ∈ Nb i, t * g * t⁻¹ = q * g * q⁻¹ := by
  classical
  set C := natC ρ Nbar with hCdef
  have htinv : t⁻¹ ∈ normalizer (Nbar : Set X) := inv_mem ht
  have hfix' : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ t⁻¹ v = v := by
    intro v hv
    calc ρ t⁻¹ v = ρ t⁻¹ (ρ t v) := by rw [hfix v hv]
      _ = v := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hM : ∀ j, ∀ y ∈ natIi ρ Nbar (Nb j), ρ t y ∈ natIi ρ Nbar (Nb j) ⊔ C :=
    fun j => d.maps_Ii j hQN hQ2 himg ht hfix
  have hM' : ∀ j, ∀ y ∈ natIi ρ Nbar (Nb j), ρ t⁻¹ y ∈ natIi ρ Nbar (Nb j) ⊔ C :=
    fun j => d.maps_Ii j hQN hQ2 himg htinv hfix'
  refine ⟨fun h hh => d.conj_mem_factor i ht (fun j _ => hM' j) hh, ?_⟩
  obtain ⟨q, hqP, hq⟩ := d.exists_proj_of_stab i hQN hQ2 hQi himg ht hfix hk
  have hqNb : q ∈ Nb i := d.proj_le i Q hqP
  have hqN : q ∈ Nbar := d.le i hqNb
  have hqinv : ∀ y, ρ q⁻¹ (ρ q y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hAC_inv : ∀ g ∈ Nbar, ∀ j, ∀ v ∈ natIi ρ Nbar (Nb j) ⊔ C,
      ρ g v ∈ natIi ρ Nbar (Nb j) ⊔ C := by
    intro g hg j v hv
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, natC_fix hg hc]
    exact Submodule.add_mem_sup (d.inv_Ii hg j a ha) hc
  have ht'N : q⁻¹ * t ∈ normalizer (Nbar : Set X) :=
    Subgroup.mul_mem _ (inv_mem (Subgroup.le_normalizer hqN)) ht
  have hM1 : ∀ j, ∀ y ∈ natIi ρ Nbar (Nb j), ρ (q⁻¹ * t) y ∈ natIi ρ Nbar (Nb j) ⊔ C := by
    intro j y hy
    rw [map_mul, Module.End.mul_apply]
    exact hAC_inv q⁻¹ (inv_mem hqN) j _ (hM j y hy)
  have hM1' : ∀ j, ∀ y ∈ natIi ρ Nbar (Nb j),
      ρ (q⁻¹ * t)⁻¹ y ∈ natIi ρ Nbar (Nb j) ⊔ C := by
    intro j y hy
    rw [_root_.mul_inv_rev, _root_.inv_inv, map_mul, Module.End.mul_apply]
    exact hM' j _ (d.inv_Ii hqN j y hy)
  have hi : ∀ y ∈ natIi ρ Nbar (Nb i), ρ (q⁻¹ * t) y - y ∈ C := by
    intro y hy
    have h2 : ρ (q⁻¹ * t) y - y = ρ q⁻¹ (ρ t y - ρ q y) := by
      rw [map_mul, Module.End.mul_apply, map_sub, hqinv]
    rw [h2, natC_fix (inv_mem hqN) (hq y hy)]
    exact hq y hy
  obtain ⟨hcomm, hfixI⟩ := d.step67 i ht'N hM1 hM1' hi
  refine ⟨q, hqP, fun y hy => ?_, fun g hg => ?_⟩
  · have h1 : ρ q⁻¹ (ρ t y) = y := by
      have := hfixI y hy
      rwa [map_mul, Module.End.mul_apply] at this
    calc ρ t y = ρ q (ρ q⁻¹ (ρ t y)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = ρ q y := by rw [h1]
  · have hc : q⁻¹ * t * g = g * (q⁻¹ * t) := hcomm g hg
    calc t * g * t⁻¹ = q * (q⁻¹ * t * g) * t⁻¹ := by group
      _ = q * (g * (q⁻¹ * t)) * t⁻¹ := by rw [hc]
      _ = q * g * q⁻¹ := by group

end Core25b


end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
