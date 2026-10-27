module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaTV
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Main

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

section Generic

variable {F Q : Subgroup G} {θ : ↥F →* Perm (Fin 5)}

omit [Finite G] in
theorem map_eq_top_of_sup_eq (hθs : Function.Surjective θ) (hθk : θ.ker = Q.subgroupOf F)
    (hQF : F ≤ Subgroup.normalizer (Q : Set G)) {X : Subgroup G} (hXF : X ≤ F)
    (hcov : X ⊔ Q = F) : (X.subgroupOf F).map θ = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨g, rfl⟩ := hθs σ
  have hg : (g : G) ∈ ((X ⊔ Q : Subgroup G) : Set G) := by rw [hcov]; exact g.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Q (hXF.trans hQF)] at hg
  obtain ⟨x, hx, q, hq, hxq⟩ := hg
  have hqF : q ∈ F := by
    have : q = x⁻¹ * g := by rw [← hxq]; group
    rw [this]; exact F.mul_mem (F.inv_mem (hXF hx)) g.2
  refine ⟨⟨x, hXF hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
  have hq1 : θ ⟨q, hqF⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]; exact hq
  have e : g = ⟨x, hXF hx⟩ * ⟨q, hqF⟩ := Subtype.ext hxq.symm
  rw [e, map_mul, hq1, mul_one]

theorem pCoreOf_le_of_map_eq_top (hθk : θ.ker = Q.subgroupOf F) {X : Subgroup G} (hXF : X ≤ F)
    (htop : (X.subgroupOf F).map θ = ⊤) : pCoreOf 2 X ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup (Perm (Fin 5)) := ((pCoreOf 2 X).subgroupOf F).map θ with hP
  have hPX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have hN : P.Normal := by
    refine ⟨fun p hp σ => ?_⟩
    have hσ : σ ∈ (X.subgroupOf F).map θ := by rw [htop]; exact Subgroup.mem_top σ
    obtain ⟨x, hx, rfl⟩ := hσ
    obtain ⟨y, hy, rfl⟩ := hp
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hyO : (y : G) ∈ pCoreOf 2 X := Subgroup.mem_subgroupOf.mp hy
    have hmem : (x : G) * y * (x : G)⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X hxX) y).mp hyO
    refine ⟨x * y * x⁻¹, Subgroup.mem_subgroupOf.mpr (by simpa using hmem), ?_⟩
    simp [map_mul, map_inv]
  have h2 : IsPGroup 2 P := by
    have h0 : IsPGroup 2 ((pCoreOf 2 X).subgroupOf F) := by
      have := pCoreOf_isPGroup 2 X
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe (hPX.trans hXF)).symm
    exact h0.map θ
  have hbot : P = ⊥ := by
    by_contra hne
    have hA := normal_ge_alt5 P hne
    have h60 : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card P := Subgroup.card_dvd_of_le hA
    rw [card_alt5] at h60
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at h60
    have h3 : 3 ∣ 2 ^ k := (by norm_num : 3 ∣ 60).trans h60
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  intro p hp
  have hpF : p ∈ F := hXF (hPX hp)
  have : θ ⟨p, hpF⟩ ∈ P := ⟨⟨p, hpF⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf] at this
  exact this

end Generic

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem relIndex_Qv_Qv_eq_two {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    (Qv μ).relIndex (Qv δ) = 2 := by
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ hδ
  have hδμ : δ ∈ nbrs μ := mem_nbrs_comm hμ
  have h28 : Qv μ ⊔ Qv δ = stab μ ⊓ stab δ :=
    C.h28 C.hb1 μ δ hδμ (C.bAt_eq_of_true hvμ)
  have h2 := relIndex_Qv_inf_true C.hA hδμ hvμ
  have hn : Qv δ ≤ Subgroup.normalizer (Qv μ : Set G) :=
    ((Qv_le_inf C.hA hμ).trans inf_le_right).trans (le_normalizer_pCoreOf 2 (stab μ))
  rw [← relIndex_sup_of_le_normalizer' hn, sup_comm, h28]
  exact h2

theorem eq_stab_of_cover {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ)
    {X : Subgroup G} (hXs : X ≤ stab δ) (hQX : Qv μ ≤ X) (hcov : X ⊔ Qv δ = stab δ) :
    X = stab δ := by
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ hδ
  have hδμ : δ ∈ nbrs μ := mem_nbrs_comm hμ
  have hQδn : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) := le_normalizer_pCoreOf 2 (stab δ)
  suffices hQ : Qv δ ≤ X by
    rw [← hcov, sup_eq_left.mpr hQ]
  by_contra hQ
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := C.exists_secData hδ
  have h2 := C.relIndex_Qv_Qv_eq_two hδ hμ
  have hXQ : X ⊓ Qv δ ≤ Qv μ := by
    have hle : Qv μ ⊓ Qv δ ≤ X ⊓ Qv δ := inf_le_inf_right _ hQX
    have hmul := Subgroup.relIndex_mul_relIndex (Qv μ ⊓ Qv δ) (X ⊓ Qv δ) (Qv δ) hle inf_le_right
    have h2' : (Qv μ ⊓ Qv δ).relIndex (Qv δ) = 2 := by rw [Subgroup.inf_relIndex_right]; exact h2
    rw [h2'] at hmul
    have hne1 : (X ⊓ Qv δ).relIndex (Qv δ) ≠ 1 := by
      intro h1
      exact hQ ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_left)
    have hne0 : (X ⊓ Qv δ).relIndex (Qv δ) ≠ 0 := relIndex_ne_zero_of_finite _ _
    have hlow : (Qv μ ⊓ Qv δ).relIndex (X ⊓ Qv δ) = 1 := by
      have h0 : (Qv μ ⊓ Qv δ).relIndex (X ⊓ Qv δ) ≠ 0 := relIndex_ne_zero_of_finite _ _
      rcases Nat.lt_or_ge ((Qv μ ⊓ Qv δ).relIndex (X ⊓ Qv δ)) 2 with h | h
      · omega
      · have : 2 ≤ (X ⊓ Qv δ).relIndex (Qv δ) := by omega
        nlinarith
    exact (Subgroup.relIndex_eq_one.mp hlow).trans inf_le_left
  have htop := map_eq_top_of_sup_eq hθs hθk hQδn hXs hcov
  have hO2 := pCoreOf_le_of_map_eq_top hθk hXs htop
  have hcardX : (X ⊓ Qv δ).relIndex X = 120 := by
    rw [relIndex_inf_eq_card_map hθk hXs, htop, Subgroup.card_top, card_perm5]
  have hQμs : Qv μ ≤ stab δ := Qv_le_stab_of_mem_nbrs C.hA hδμ
  have hcardQ : (Qv μ ⊓ Qv δ).relIndex (Qv μ) = 8 := by
    rw [relIndex_inf_eq_card_map hθk hQμs]
    have h28 : Qv μ ⊔ Qv δ = stab μ ⊓ stab δ :=
      C.h28 C.hb1 μ δ hδμ (C.bAt_eq_of_true hvμ)
    have hcov' : Qv μ ⊔ Qv δ = stab δ ⊓ stab μ := by rw [h28, inf_comm]
    have himg : (((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ) =
        ((Qv μ).subgroupOf (stab δ)).map θ := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        have hg' : (g : G) ∈ ((Qv μ ⊔ Qv δ : Subgroup G) : Set G) := by
          rw [hcov']; exact Subgroup.mem_subgroupOf.mp hg
        rw [Subgroup.coe_mul_of_left_le_normalizer_right (Qv μ) (Qv δ)
          (hQμs.trans hQδn)] at hg'
        obtain ⟨x, hx, q, hq, hxq⟩ := hg'
        have hqs : q ∈ stab δ := pCoreOf_le 2 _ hq
        refine ⟨⟨x, hQμs hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
        have hq1 : θ ⟨q, hqs⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]; exact hq
        have e : g = ⟨x, hQμs hx⟩ * ⟨q, hqs⟩ := Subtype.ext hxq.symm
        rw [e, map_mul, hq1, mul_one]
      · exact Subgroup.map_mono (Subgroup.subgroupOf_mono _
          (le_inf hQμs (pCoreOf_le 2 _)))
    rw [← himg, ← relIndex_inf_eq_card_map hθk inf_le_left, Subgroup.inf_relIndex_left]
    exact relIndex_Qv_inf_false C.hA hμ hδ
  have hXQeq : X ⊓ Qv δ = Qv μ ⊓ Qv δ :=
    le_antisymm (le_inf hXQ inf_le_right) (inf_le_inf_right _ hQX)
  have h15 : (Qv μ).relIndex X = 15 := by
    have hmul := Subgroup.relIndex_mul_relIndex (Qv μ ⊓ Qv δ) (Qv μ) X inf_le_left hQX
    rw [hcardQ, ← hXQeq, hcardX] at hmul
    omega
  have hsig : SitSigma δ μ X := by
    refine ⟨hμ, hXs, ?_, ?_, ?_⟩
    · rw [inf_eq_left.mpr hQX]
      refine ⟨hQX, pCoreOf_isPGroup 2 _, ?_⟩
      show ¬ 2 ∣ (Qv μ).relIndex X
      rw [h15]; norm_num
    · have hZQ : Zv μ ≤ Qv δ := C.Zv_le_Qv_of_true hvμ (by
        rw [dist_eq_one_iff_adj.mpr hδμ]; have := C.hb5; omega)
      have hZX : Zv μ ≤ X ⊓ Qv δ := le_inf ((Zv_le_Qv C.hA μ).trans hQX) hZQ
      refine hZX.trans (le_pCoreOf_of_le_normalizer inf_le_left ?_ ?_)
      · refine X1512.le_normalizer_of_forall fun f hf x hx => ⟨X.mul_mem (X.mul_mem hf hx.1)
          (X.inv_mem hf), (Subgroup.mem_normalizer_iff.mp (hQδn (hXs hf)) x).mp hx.2⟩
      · exact (pCoreOf_isPGroup 2 (stab δ)).to_le inf_le_right
    · apply le_antisymm (sup_le hXs inf_le_left)
      calc stab δ = X ⊔ Qv δ := hcov.symm
        _ ≤ X ⊔ (stab δ ⊓ stab μ) := sup_le_sup_left (Qv_le_inf C.hA hμ) _
  exact sitSigma_false_nonresidual C.hA C.hb1 hsig hQX (Or.inl hO2)

theorem oTwoRes_le_cSecIn_of_normal {δ : Geo H M} (hδ : vtype δ = false) {A U W : Subgroup G}
    (hsec : IsSec (stab δ) A U) (hWs : W ≤ stab δ) (hWQ : ¬ W ≤ Qv δ)
    (hW : ∀ w ∈ W, ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ A) :
    oTwoRes (stab δ) ≤ cSecIn (stab δ) A U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := C.exists_secData hδ
  set K := cSecIn (stab δ) A U with hK
  have hmemK : ∀ g, g ∈ K ↔ g ∈ stab δ ∧ ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ A :=
    fun g => mem_cSecIn_iff hsec.normL
  have hKn : ∀ g ∈ stab δ, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨hks, hkU⟩ := (hmemK k).mp hk
    refine (hmemK _).mpr ⟨(stab δ).mul_mem ((stab δ).mul_mem hg hks) ((stab δ).inv_mem hg),
      fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ U := by
      have := hsec.conj_mem_N ⟨g⁻¹, (stab δ).inv_mem hg⟩ ⟨u, hu⟩
      simpa using this
    have h1 := hsec.conj_mem_L hg (hkU _ hu')
    have e : g * k * g⁻¹ * u * (g * k * g⁻¹)⁻¹ * u⁻¹ =
        g * (k * (g⁻¹ * u * g) * k⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by group
    rw [e]; exact h1
  set P : Subgroup (Perm (Fin 5)) := (K.subgroupOf (stab δ)).map θ with hP
  have hPn : P.Normal := by
    refine ⟨fun p hp σ => ?_⟩
    obtain ⟨g, rfl⟩ := hθs σ
    obtain ⟨k, hk, rfl⟩ := hp
    refine ⟨g * k * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa using hKn g g.2 k (Subgroup.mem_subgroupOf.mp hk)
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply hWQ
    intro w hw
    have hwK : w ∈ K := (hmemK w).mpr ⟨hWs hw, hW w hw⟩
    have : θ ⟨w, hWs hw⟩ ∈ P := ⟨⟨w, hWs hw⟩, Subgroup.mem_subgroupOf.mpr hwK, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf] at this
    exact this
  have hAP := normal_ge_alt5 P hPne
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hxs, m, hm, hxm⟩
  obtain ⟨hxs', hxA⟩ := psi_mem_alt_of_mem_oTwoRes θ
    (Subgroup.subset_closure ⟨hxs, m, hm, hxm⟩ : x ∈ oTwoRes (stab δ))
  obtain ⟨k, hk, hkx⟩ := hAP hxA
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  set q : ↥(stab δ) := k⁻¹ * ⟨x, hxs⟩ with hq
  have hqQ : (q : G) ∈ Qv δ := by
    have : θ q = 1 := by rw [hq, map_mul, map_inv, hkx, inv_mul_cancel]
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf] at this
    exact this
  have hxkq : (⟨x, hxs⟩ : ↥(stab δ)) = k * q := by rw [hq]; group
  have hck : hsec.conjHom k = 1 := hsec.conjHom_eq_one ((hmemK _).mp hkK).2
  have hcx : hsec.conjHom ⟨x, hxs⟩ = hsec.conjHom q := by
    rw [hxkq, map_mul, hck, one_mul]
  obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 (stab δ)) ⟨q, hqQ⟩
  have hqe : q ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
  have h1 : orderOf (hsec.conjHom ⟨x, hxs⟩) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow]; rw [show (⟨x, hxs⟩ : ↥(stab δ)) ^ m = 1 from
      Subtype.ext (by simpa using hxm), map_one])
  have h2 : orderOf (hsec.conjHom ⟨x, hxs⟩) ∣ 2 ^ e :=
    orderOf_dvd_of_pow_eq_one (by rw [hcx, ← map_pow, hqe, map_one])
  have hcop : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have h3 : orderOf (hsec.conjHom ⟨x, hxs⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  refine (hmemK x).mpr ⟨hxs, fun u hu => ?_⟩
  have key : ∀ v ∈ U, x * v⁻¹ * x⁻¹ * v ∈ A := by
    intro v hv
    have h4 := congrArg (fun φ => φ (hsec.proj ⟨v, hv⟩)) h3
    simp only [MulAut.one_apply] at h4
    have h5 : hsec.proj (hsec.conjN ⟨x, hxs⟩ ⟨v, hv⟩) = hsec.proj ⟨v, hv⟩ := h4
    rw [hsec.proj_eq_proj_iff] at h5
    simpa [IsSec.conjN, mul_assoc] using h5
  simpa using key u⁻¹ (U.inv_mem hu)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
