module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Defs
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.NatAPI
public import CFSG.Quasithin.EmptyFaithful.SzF53B3EStep
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Gen

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

section Sections

theorem relIndex_fixSecIn_zpowers_le {A J U D : Subgroup G} {y : G} (hAD : A ≤ D)
    (hDJ : D ≤ J) (hUJ : U ≤ J) (hyJ : y ∈ Subgroup.normalizer (J : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hJA : J ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ x ∈ J, ∀ x' ∈ J, x * x' * x⁻¹ * x'⁻¹ ∈ A)
    (hc : ∀ u ∈ U, u * y * u⁻¹ * y⁻¹ ∈ D) :
    (fixSecIn (Subgroup.zpowers y) A J).relIndex J ≤ (U ⊔ A).relIndex J * A.relIndex D := by
  have hAJ : A ≤ J := hAD.trans hDJ
  have hN : (A.subgroupOf J).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hJA g.2) x).mp hx⟩
  have hmem : ∀ x : ↥J, y * (x : G) * y⁻¹ * (x : G)⁻¹ ∈ J := fun x =>
    J.mul_mem ((Subgroup.mem_normalizer_iff.mp hyJ x).mp x.2) (J.inv_mem x.2)
  let f : ↥J →* ↥J ⧸ A.subgroupOf J :=
    { toFun := fun x => QuotientGroup.mk ⟨y * (x : G) * y⁻¹ * (x : G)⁻¹, hmem x⟩
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simp
      map_mul' := fun x x' => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hb : y * (x' : G) * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hyJ x').mp x'.2
        have h1 := hcomm _ (J.inv_mem hb) _ (J.inv_mem x.2)
        have h2 := (Subgroup.mem_normalizer_iff.mp (hJA (J.mul_mem x'.2 x.2)) _).mp h1
        have h3 := hcomm _ x.2 _ x'.2
        convert A.mul_mem h3 h2 using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group }
  have hf : ∀ x : ↥J, f x = QuotientGroup.mk ⟨y * (x : G) * y⁻¹ * (x : G)⁻¹, hmem x⟩ :=
    fun _ => rfl
  have hker : f.ker = (fixSecIn (Subgroup.zpowers y) A J).subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, mem_fixSecIn_zpowers_iff hJA hyA]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  set U' : Subgroup ↥J := (U ⊔ A).subgroupOf J with hU'
  have hUD : U'.map f ≤ (D.subgroupOf J).map (QuotientGroup.mk' (A.subgroupOf J)) := by
    rw [Subgroup.map_le_iff_le_comap]
    set T := ((D.subgroupOf J).map (QuotientGroup.mk' (A.subgroupOf J))).comap f with hT
    have hTmem : ∀ x : ↥J, y * (x : G) * y⁻¹ * (x : G)⁻¹ ∈ D → x ∈ T := fun x hx =>
      ⟨⟨_, hmem x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hle : U ⊔ A ≤ T.map J.subtype := by
      refine sup_le (fun u hu => ⟨⟨u, hUJ hu⟩, hTmem _ ?_, rfl⟩)
        (fun a ha => ⟨⟨a, hAJ ha⟩, hTmem _ ?_, rfl⟩)
      · have := D.inv_mem (hc u hu)
        simpa [mul_assoc] using this
      · have h1 := (Subgroup.mem_normalizer_iff.mp hyA a).mp ha
        exact hAD (A.mul_mem h1 (A.inv_mem ha))
    intro x hx
    obtain ⟨t, ht, htx⟩ := hle (Subgroup.mem_subgroupOf.mp hx)
    have : t = x := Subtype.ext htx
    rw [← this]
    exact ht
  have hcardD : Nat.card ((D.subgroupOf J).map (QuotientGroup.mk' (A.subgroupOf J))) =
      A.relIndex D := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hDJ]
  have h1 : (fixSecIn (Subgroup.zpowers y) A J).relIndex J = f.ker.index := by
    rw [hker]; rfl
  have h2 : f.ker.index = f.ker.relIndex (U' ⊔ f.ker) * (U' ⊔ f.ker).index :=
    (Subgroup.relIndex_mul_index le_sup_right).symm
  have h3 : f.ker.relIndex (U' ⊔ f.ker) = Nat.card (U'.map f) := by
    rw [Subgroup.relIndex_sup_right, Subgroup.relIndex_ker]
  have h4 : (U' ⊔ f.ker).index ≤ U'.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le le_sup_left)
  have h5 : Nat.card (U'.map f) ≤ A.relIndex D := by
    rw [← hcardD]
    exact Subgroup.card_le_of_le hUD
  have h6 : U'.index = (U ⊔ A).relIndex J := rfl
  rw [h1, h2, h3, ← h6]
  calc Nat.card (U'.map f) * (U' ⊔ f.ker).index ≤ A.relIndex D * U'.index :=
        Nat.mul_le_mul h5 h4
    _ = U'.index * A.relIndex D := Nat.mul_comm _ _

theorem mem_of_odd_two_step {A J B : Subgroup G} {z : G} {m : ℕ} (hm : Odd m) (hzm : z ^ m = 1)
    (hJB : J ≤ B) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hzA : z ∈ Subgroup.normalizer (A : Set G)) (hJsq : ∀ x ∈ J, x * x ∈ A)
    (h1 : ∀ x ∈ J, z * x * z⁻¹ * x⁻¹ ∈ A) (h2 : ∀ x ∈ B, z * x * z⁻¹ * x⁻¹ ∈ J) :
    ∀ x ∈ B, z * x * z⁻¹ * x⁻¹ ∈ A := by
  intro x hx
  set c := z * x * z⁻¹ * x⁻¹ with hc
  have hcJ : c ∈ J := h2 x hx
  have hcB : c ∈ B := hJB hcJ
  have key : ∀ k : ℕ, (z ^ k * x * (z ^ k)⁻¹) * x⁻¹ * (c ^ k)⁻¹ ∈ A := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzc : z * c * z⁻¹ * c⁻¹ ∈ A := h1 c hcJ
      set a := (z ^ k * x * (z ^ k)⁻¹) * x⁻¹ * (c ^ k)⁻¹ with ha
      have hzk : z ^ k * x * (z ^ k)⁻¹ = a * c ^ k * x := by rw [ha]; group
      have hzk1 : z ^ (k + 1) * x * (z ^ (k + 1))⁻¹ = z * (a * c ^ k * x) * z⁻¹ := by
        rw [← hzk]; group
      rw [hzk1]
      have hza : z * a * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hzA a).mp ih
      have hzck : z * c ^ k * z⁻¹ = (z * c * z⁻¹) ^ k := by
        rw [← conj_pow]
      have hpow : ∀ j : ℕ, (z * c * z⁻¹) ^ j * (c ^ j)⁻¹ ∈ A := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hcA : c ^ j ∈ Subgroup.normalizer (A : Set G) :=
            Subgroup.pow_mem _ (hBA hcB) j
          have e : (z * c * z⁻¹) ^ (j + 1) * (c ^ (j + 1))⁻¹ =
              ((z * c * z⁻¹) ^ j * (c ^ j)⁻¹) *
                (c ^ j * ((z * c * z⁻¹ * c⁻¹)) * (c ^ j)⁻¹) := by
            rw [pow_succ, pow_succ]; group
          rw [e]
          exact A.mul_mem ihj ((Subgroup.mem_normalizer_iff.mp hcA _).mp hzc)
      have e2 : z * (a * c ^ k * x) * z⁻¹ * x⁻¹ * (c ^ (k + 1))⁻¹ =
          (z * a * z⁻¹) * ((z * c ^ k * z⁻¹) * (c ^ k)⁻¹) *
            (c ^ k * (z * x * z⁻¹ * x⁻¹ * c⁻¹) * (c ^ k)⁻¹) := by
        rw [pow_succ]; group
      rw [e2]
      have hcc : z * x * z⁻¹ * x⁻¹ * c⁻¹ = 1 := by rw [hc]; group
      rw [hcc, mul_one, mul_inv_cancel, mul_one, hzck]
      exact A.mul_mem hza (hpow k)
  have hm' := key m
  rw [hzm, one_mul, inv_one, mul_one, mul_inv_cancel, one_mul] at hm'
  have hcm : c ^ m ∈ A := by simpa using A.inv_mem hm'
  obtain ⟨r, rfl⟩ := hm
  have hc2 : c ^ 2 ∈ A := by rw [pow_two]; exact hJsq c hcJ
  have hc2r : (c ^ 2) ^ r ∈ A := A.pow_mem hc2 r
  have e : c = c ^ (2 * r + 1) * ((c ^ 2) ^ r)⁻¹ := by
    rw [← pow_mul, pow_succ]; group
  rw [e]
  exact A.mul_mem hcm (A.inv_mem hc2r)

open scoped Pointwise in
theorem relIndex_sup_of_le_normalizer' {H K : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (K : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE K
    (le_sup_left : H ≤ H ⊔ K)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE K
    (le_sup_left : H ≤ H ⊔ K)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (H : Set G) * (K : Set G) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right H K hH) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

end Sections

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem tv_induction {δ : Geo H M} (hδ : vtype δ = false) {y : G} (hy : y ∈ stab δ)
    (hyQ : y ∉ Qv δ) (hyL : y ∈ oTwoRes (stab δ) ⊔ Qv δ) :
    ∀ (n : ℕ) (A B : Subgroup G), A.relIndex B = n →
      IsNormalIn (stab δ) (Wnn δ) A → IsNormalIn (stab δ) (Wnn δ) B → A ≤ B →
      ((∃ D : Subgroup G, A ≤ D ∧ D ≤ B ∧ A.relIndex D ≤ 2 ∧
          ∀ x ∈ B, x * y * x⁻¹ * y⁻¹ ∈ D) ∨
        (∃ U : Subgroup G, A ≤ U ∧ U ≤ B ∧ U.relIndex B ≤ 2 ∧
          ∀ u ∈ U, u * y * u⁻¹ * y⁻¹ ∈ A)) →
      oTwoRes (stab δ) ≤ cSecIn (stab δ) A B := by
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := C.exists_secData hδ
  have hker : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ := by
    intro x
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]
  have hθy1 : θ ⟨y, hy⟩ ≠ 1 := fun h => hyQ ((hker _).mp h)
  have hθyA : θ ⟨y, hy⟩ ∈ alternatingGroup (Fin 5) :=
    (S34.mem_sup_iff_alt hθs hθk hy).mp hyL
  have hWX : Wnn δ ≤ stab δ := (C.Wnn_le_Qv hδ).trans (pCoreOf_le 2 _)
  have hWQ : Wnn δ ≤ pCoreOf 2 (stab δ) := C.Wnn_le_Qv hδ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B hn hA hB hAB hsm
  have hXA : stab δ ≤ Subgroup.normalizer (A : Set G) := D14.le_normalizer_of_isNormalIn hA
  have hXB : stab δ ≤ Subgroup.normalizer (B : Set G) := D14.le_normalizer_of_isNormalIn hB
  have hBX : B ≤ stab δ := hB.1.trans hWX
  rcases eq_or_lt_of_le hAB with hAB' | hAB'
  ·
    subst hAB'
    intro l hl
    have hlX : l ∈ stab δ := oTwoRes_le _ hl
    rw [mem_cSecIn_iff hXA]
    exact ⟨hlX, fun x hx => A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXA hlX) x).mp hx)
      (A.inv_mem hx)⟩
  obtain ⟨J, hJ, hJB⟩ := F53B3.NoE.exists_chiefStep_of_lt hA hB hAB'
  have hAJ : A < J := hJ.2.2.1
  have hsec : IsSec (stab δ) A J := isSec_of_chiefStep hWX hWQ hJ
  have hQc : pCoreOf 2 (stab δ) ≤ cSecIn (stab δ) A J :=
    pCoreOf_le_cSecIn_of_chiefStep hWX hWQ hJ
  have hk : θ.ker ≤ (cSecIn (stab δ) A J).subgroupOf (stab δ) := by
    rw [hθk]
    exact Subgroup.subgroupOf_mono _ hQc
  have hNAJ : (A.subgroupOf J).Normal := hsec.normal_subgroupOf
  have hXJ : stab δ ≤ Subgroup.normalizer (J : Set G) := hsec.normN
  have hJX : J ≤ stab δ := hJB.trans hBX
  have hyJ : ∀ x ∈ J, x * y * x⁻¹ * y⁻¹ ∈ J := fun x hx =>
    J.mul_mem (J.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hXJ hy) _).mp (J.inv_mem hx)) |>
      fun h => by simpa [mul_assoc] using h) (J.inv_mem (J.one_mem)) |> fun h => by
        simpa [mul_assoc] using h
  have hsmall : (fixSecIn (Subgroup.zpowers y) A J).relIndex J ≤ 2 := by
    have hcomm : ∀ x ∈ J, ∀ x' ∈ J, x * x' * x⁻¹ * x'⁻¹ ∈ A := hsec.comm
    rcases hsm with ⟨D, hAD, hDB, hD2, hD⟩ | ⟨U, hAU, hUB, hU2, hU⟩
    · have hle := relIndex_fixSecIn_zpowers_le (U := J) (D := D ⊓ J) (le_inf hAD hAJ.le)
        inf_le_right le_rfl (hXJ hy) (hXA hy) (hJX.trans hXA) hcomm
        (fun u hu => ⟨hD u (hJB hu), hyJ u hu⟩)
      have h1 : (J ⊔ A).relIndex J = 1 := by
        rw [sup_eq_left.mpr hAJ.le, Subgroup.relIndex_self]
      have h2 : A.relIndex (D ⊓ J) ≤ A.relIndex D :=
        Subgroup.relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_of_finite _ _)
      rw [h1, one_mul] at hle
      omega
    · have hle := relIndex_fixSecIn_zpowers_le (U := U ⊓ J) (D := A) le_rfl hAJ.le
        inf_le_right (hXJ hy) (hXA hy) (hJX.trans hXA) hcomm (fun u hu => hU u hu.1)
      have h1 : (U ⊓ J ⊔ A).relIndex J ≤ 2 := by
        rw [sup_eq_left.mpr (le_inf hAU hAJ.le), Subgroup.inf_relIndex_right]
        exact (Subgroup.relIndex_le_of_le_right hJB (relIndex_ne_zero_of_finite _ _)).trans hU2
      rw [Subgroup.relIndex_self, mul_one] at hle
      omega
  set Mo := secModule hsec θ hθs hk with hMo
  have hsd : SecData Mo (stab δ) A J θ (MonoidHom.id _) := by
    refine ⟨fun x => ⟨x, rfl⟩, fun x y h => h, ?_⟩
    intro k u x hux
    have hu : u = hsec.proj x := hux
    subst hu
    exact ⟨hsec.conj_mem_N k x, secModule_act_proj hsec θ hθs hk k x⟩
  have hidx : idx Mo (θ ⟨y, hy⟩) ≤ 2 := by
    rw [← hsd.secIdx_eq_idx hsec.le hy]
    exact hsmall
  have htop : fixW Mo (alternatingGroup (Fin 5)) = ⊤ := by
    by_contra hne
    have h4 := cf Mo hne hθyA hθy1
    have h4' : 4 ≤ cfm (θ ⟨y, hy⟩) := by
      unfold cfm
      split_ifs <;> norm_num
    omega
  have hLJ : oTwoRes (stab δ) ≤ cSecIn (stab δ) A J := by
    intro l hl
    obtain ⟨hlX, hlA⟩ := psi_mem_alt_of_mem_oTwoRes θ hl
    have hact : Mo.act (θ ⟨l, hlX⟩) = 1 := by
      ext w
      have hw : w ∈ fixW Mo (alternatingGroup (Fin 5)) := by
        rw [htop]; exact Subgroup.mem_top w
      exact hw _ hlA
    exact (secModule_act_eq_one_iff hsec θ hθs hk ⟨l, hlX⟩).mp hact
  have hJB' : oTwoRes (stab δ) ≤ cSecIn (stab δ) J B := by
    have hlt : J.relIndex B < n := by
      rw [← hn, ← Subgroup.relIndex_mul_relIndex A J B hAJ.le hJB]
      have h1 : A.relIndex J ≠ 1 := fun h => hAJ.2 (Subgroup.relIndex_eq_one.mp h)
      have h0 : A.relIndex J ≠ 0 := relIndex_ne_zero_of_finite _ _
      have h0' : J.relIndex B ≠ 0 := relIndex_ne_zero_of_finite _ _
      have : 2 ≤ A.relIndex J := by omega
      nlinarith [Nat.pos_of_ne_zero h0']
    refine ih _ hlt J B rfl hJ.1 hB hJB ?_
    rcases hsm with ⟨D, hAD, hDB, hD2, hD⟩ | ⟨U, hAU, hUB, hU2, hU⟩
    · refine Or.inl ⟨D ⊔ J, le_sup_right, sup_le hDB hJB, ?_, fun x hx => Subgroup.mem_sup_left (hD x hx)⟩
      rw [relIndex_sup_of_le_normalizer' ((hDB.trans hBX).trans hXJ)]
      exact (Subgroup.relIndex_le_of_le_left hAJ.le (relIndex_ne_zero_of_finite _ _)).trans hD2
    · refine Or.inr ⟨U ⊔ J, le_sup_right, sup_le hUB hJB, ?_, ?_⟩
      · exact (Subgroup.relIndex_le_of_le_left le_sup_left
          (relIndex_ne_zero_of_finite _ _)).trans hU2
      · have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hBX.trans hXJ
        have hle : U ⊔ J ≤ fixSecIn (Subgroup.zpowers y) J B := by
          refine sup_le (fun u hu => ?_) (fun x hx => ?_)
          · rw [mem_fixSecIn_zpowers_iff hBJ (hXJ hy)]
            refine ⟨hUB hu, hAJ.le ?_⟩
            have := A.inv_mem (hU u hu)
            simpa [mul_assoc] using this
          · rw [mem_fixSecIn_zpowers_iff hBJ (hXJ hy)]
            refine ⟨hJB hx, J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXJ hy) x).mp hx)
              (J.inv_mem hx)⟩
        intro u hu
        have h1 := ((mem_fixSecIn_zpowers_iff hBJ (hXJ hy)).mp (hle hu)).2
        have := J.inv_mem h1
        simpa [mul_assoc] using this
  rw [oTwoRes, Subgroup.closure_le]
  rintro z ⟨hzX, m, hm, hzm⟩
  have hzL : z ∈ oTwoRes (stab δ) := Subgroup.subset_closure ⟨hzX, m, hm, hzm⟩
  rw [SetLike.mem_coe, mem_cSecIn_iff hXA]
  refine ⟨hzX, mem_of_odd_two_step hm hzm hJB (hBX.trans hXA) (hXA hzX)
    (fun x hx => by rw [← pow_two]; exact hsec.sq x hx) ?_ ?_⟩
  · exact ((mem_cSecIn_iff hXA).mp (hLJ hzL)).2
  · exact ((mem_cSecIn_iff hXJ).mp (hJB' hzL)).2

theorem false_of_small_action {δ : Geo H M} (hδ : vtype δ = false)
    {y : G} (hy : y ∈ stab δ) (hyQ : y ∉ Qv δ) (hyL : y ∈ oTwoRes (stab δ) ⊔ Qv δ)
    {U D : Subgroup G} (hUW : U ≤ Wnn δ) (hVD : Vn δ ≤ D) (hDW : D ≤ Wnn δ)
    (hidx : (U ⊔ Vn δ).relIndex (Wnn δ) * (Vn δ).relIndex D ≤ 2)
    (hc : ∀ u ∈ U, u * y * u⁻¹ * y⁻¹ ∈ D) : False := by
  have hWX : Wnn δ ≤ stab δ := (C.Wnn_le_Qv hδ).trans (pCoreOf_le 2 _)
  have hXV : stab δ ≤ Subgroup.normalizer (Vn δ : Set G) := stab_le_normalizer_Vn δ
  have hXW : stab δ ≤ Subgroup.normalizer (Wnn δ : Set G) := stab_le_normalizer_Wnn δ
  have hV : IsNormalIn (stab δ) (Wnn δ) (Vn δ) :=
    ⟨Vn_le_Wnn_self δ, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hXV hg) x).mp hx⟩
  have hW : IsNormalIn (stab δ) (Wnn δ) (Wnn δ) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hXW hg) x).mp hx⟩
  have hWV : Wnn δ ≤ Subgroup.normalizer (Vn δ : Set G) := hWX.trans hXV
  have hsm : (∃ D' : Subgroup G, Vn δ ≤ D' ∧ D' ≤ Wnn δ ∧ (Vn δ).relIndex D' ≤ 2 ∧
        ∀ x ∈ Wnn δ, x * y * x⁻¹ * y⁻¹ ∈ D') ∨
      (∃ U' : Subgroup G, Vn δ ≤ U' ∧ U' ≤ Wnn δ ∧ U'.relIndex (Wnn δ) ≤ 2 ∧
        ∀ u ∈ U', u * y * u⁻¹ * y⁻¹ ∈ Vn δ) := by
    have h1 : (U ⊔ Vn δ).relIndex (Wnn δ) ≠ 0 := relIndex_ne_zero_of_finite _ _
    have h2 : (Vn δ).relIndex D ≠ 0 := relIndex_ne_zero_of_finite _ _
    by_cases hD1 : (Vn δ).relIndex D = 1
    ·
      have hDV : D ≤ Vn δ := Subgroup.relIndex_eq_one.mp hD1
      right
      refine ⟨U ⊔ Vn δ, le_sup_right, sup_le hUW (Vn_le_Wnn_self δ), ?_, ?_⟩
      · rw [hD1, mul_one] at hidx; exact hidx
      have hle : U ⊔ Vn δ ≤ fixSecIn (Subgroup.zpowers y) (Vn δ) (Wnn δ) := by
        refine sup_le (fun u hu => ?_) (fun v hv => ?_)
        · rw [mem_fixSecIn_zpowers_iff hWV (hXV hy)]
          refine ⟨hUW hu, hDV ?_⟩
          have := D.inv_mem (hc u hu)
          simpa [mul_assoc] using this
        · rw [mem_fixSecIn_zpowers_iff hWV (hXV hy)]
          exact ⟨Vn_le_Wnn_self δ hv, (Vn δ).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hXV hy) v).mp hv) ((Vn δ).inv_mem hv)⟩
      intro u hu
      have h := ((mem_fixSecIn_zpowers_iff hWV (hXV hy)).mp (hle hu)).2
      have := (Vn δ).inv_mem h
      simpa [mul_assoc] using this
    ·
      have hU1 : (U ⊔ Vn δ).relIndex (Wnn δ) = 1 := by
        by_contra hne
        have h3 : 2 ≤ (U ⊔ Vn δ).relIndex (Wnn δ) := by omega
        have h4 : 2 ≤ (Vn δ).relIndex D := by omega
        nlinarith
      have hWU : Wnn δ ≤ U ⊔ Vn δ := Subgroup.relIndex_eq_one.mp hU1
      left
      refine ⟨D, hVD, hDW, ?_, fun x hx => ?_⟩
      · rw [hU1, one_mul] at hidx; exact hidx
      have hx' : x ∈ ((U ⊔ Vn δ : Subgroup G) : Set G) := hWU hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right U (Vn δ) (hUW.trans hWV)] at hx'
      obtain ⟨u, hu, v, hv, rfl⟩ := hx'
      have hvy : v * y * v⁻¹ * y⁻¹ ∈ Vn δ := by
        have h5 := (Subgroup.mem_normalizer_iff.mp (hXV hy) _).mp ((Vn δ).inv_mem hv)
        have e : v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
        rw [e]; exact (Vn δ).mul_mem hv h5
      have h6 : u * (v * y * v⁻¹ * y⁻¹) * u⁻¹ ∈ Vn δ :=
        (Subgroup.mem_normalizer_iff.mp (hWV (hUW hu)) _).mp hvy
      have e : u * v * y * (u * v)⁻¹ * y⁻¹ =
          (u * (v * y * v⁻¹ * y⁻¹) * u⁻¹) * (u * y * u⁻¹ * y⁻¹) := by group
      rw [e]
      exact D.mul_mem (hVD h6) (hc u hu)
  have hL := C.tv_induction hδ hy hyQ hyL _ (Vn δ) (Wnn δ) rfl hV hW (Vn_le_Wnn_self δ) hsm
  obtain ⟨ν, hν⟩ := exists_adj δ
  have hνn : ν ∈ nbrs δ := hν
  have hvν : vtype ν = true := vtype_true_of_mem_nbrs_false hνn hδ
  have hδν : δ ∈ nbrs ν := mem_nbrs_comm hνn
  have hKle : Wn ν ≤ stab δ ⊓ stab ν :=
    le_inf ((C.Wn_le_Qv hvν).trans (Qv_le_stab_of_mem_nbrs C.hA hδν))
      ((C.Wn_le_Qv hvν).trans (pCoreOf_le 2 _))
  have hLK : oTwoRes (stab δ) ≤ Subgroup.normalizer (Wn ν : Set G) :=
    X1512.le_normalizer_of_forall fun l hl w hw => by
      have hwW : w ∈ Wnn δ := Wn_le_Wnn hνn hw
      have h1 := ((mem_cSecIn_iff hXV).mp (hL hl)).2 w hwW
      have e : l * w * l⁻¹ = (l * w * l⁻¹ * w⁻¹) * w := by group
      rw [e]
      exact (Wn ν).mul_mem (Vn_le_Wn hδν h1) hw
  have hδK : stab δ ≤ Subgroup.normalizer (Wn ν : Set G) := by
    intro g hg
    obtain ⟨hgm, hgfix⟩ := mem_stab.mp hg
    set g' : ↥(H ⊔ M) := ⟨g, hgm⟩
    have hgν : g' • ν ∈ nbrs δ := by
      have := (smul_adj g').mpr hνn
      rw [hgfix] at this
      exact this
    obtain ⟨l, hlL, hlν⟩ := C.exists_oTwoRes_smul hνn hgν
    have hh : ((l⁻¹ * g' : ↥(H ⊔ M)) : G) ∈ stab ν := by
      apply mem_stab_of_smul_eq
      rw [mul_smul, ← hlν, inv_smul_smul]
    have e : g = (l : G) * ((l⁻¹ * g' : ↥(H ⊔ M)) : G) := by
      simp [g']
    rw [e]
    exact Subgroup.mul_mem _ (hLK hlL) (stab_le_normalizer_Wn ν hh)
  have hbot := eq_bot_of_normalizes_both C.hA hν hKle hδK (stab_le_normalizer_Wn ν)
  have hVne : Vn δ ≠ ⊥ := by
    intro h
    have := Zv_le_Vn_of_mem_nbrs hνn
    rw [h] at this
    exact Zv_ne_bot C.hA ν (le_bot_iff.mp this)
  exact hVne (le_bot_iff.mp (hbot ▸ Vn_le_Wn hδν))

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
