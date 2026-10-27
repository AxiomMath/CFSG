module

public import CFSG.Quasithin.EmptyFaithful.S153Decomp
public import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.EmptyFaithful.S153Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417

section SubFacts

variable {G : Type} [Group G] [Finite G] {V M T : Subgroup G} (hV : IsElemAbelian 2 V)
  {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}

omit [Finite G] in
theorem autI_nS (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M) :
    autI hV (T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) =
      autI hV T ⊓ (L₁ ⊔ L₂) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, ⟨hgT, hgn⟩, rfl⟩ := (mem_autI hV).1 hφ
    have hgT' : convI hV g ∈ autI hV T := convI_mem_autI hV hgT g.2
    have hgX : convI hV g ∈ autI hV M := convI_mem_autI hV (hTM hgT) g.2
    refine ⟨hgT', (hS.mem_sup_iff hgX).2 fun u hu => ?_⟩
    have hst := (mem_normalizer_map_inclMod_iff hV g.2 (commV L₁)).1 hgn
    exact (mem_stabSub.1 hst u).2 hu
  · rintro ⟨hφT, hφN⟩
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hV).1 hφT
    have hst : convI hV g ∈ stabSub (commV L₁) := hS.sup_le_stab₁ hφN
    have hgn : (g : G) ∈ Subgroup.normalizer
        (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :=
      (mem_normalizer_map_inclMod_iff hV g.2 (commV L₁)).2 hst
    have hmem : (g : G) ∈ T ⊓ Subgroup.normalizer
        (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := Subgroup.mem_inf.2 ⟨hgT, hgn⟩
    exact convI_mem_autI hV hmem g.2

omit [Finite G] in
theorem inf_centralizer_le_nS (T : Subgroup G) (V₁ : Subgroup G) (hV₁ : V₁ ≤ V) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) :=
  inf_le_inf_left T ((Subgroup.centralizer_le hV₁).trans (Subgroup.centralizer_le_normalizer _))

theorem relIndex_nS_of_model (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    (T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)).relIndex T =
      2 := by
  set V₁ : Subgroup G := (commV L₁).map (inclMod hV) with hV₁
  set S : Subgroup G := T ⊓ Subgroup.normalizer (V₁ : Set G) with hSdef
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hTN
  have e1 := card_autI_mul_card_inf hV hTN
  have e2 := card_autI_mul_card_inf hV hSN
  have hV₁V : V₁ ≤ V := map_inclMod_le hV _
  have hCS : S ⊓ Subgroup.centralizer (V : Set G) = T ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf (inf_centralizer_le_nS T V₁ hV₁V) inf_le_right
  have hTbar : Nat.card (autI hV T) = 8 := hS.card_T hsyl
  have hSbar : Nat.card (autI hV S) = 4 := by
    rw [hSdef, hV₁, autI_nS hV hS hTM]
    exact hS.card_S hsyl
  have e3 := Subgroup.relIndex_mul_card S T
  rw [inf_eq_left.2 (inf_le_left : S ≤ T)] at e3
  rw [hCS, hSbar] at e2
  rw [hTbar] at e1
  set c := Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G)) with hcdef
  have hc : 0 < c := Nat.card_pos
  have key : S.relIndex T * (4 * c) = 2 * (4 * c) := by
    calc S.relIndex T * (4 * c) = S.relIndex T * Nat.card S := by rw [e2]
      _ = Nat.card T := e3
      _ = 8 * c := e1.symm
      _ = 2 * (4 * c) := by ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) key

theorem card_ZS_of_model (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
        Subgroup G) : Set G)) = 4 := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsyl
  have hSN : T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G) := inf_le_left.trans (hTM.trans hMN)
  rw [← card_fixV_autI hV hSN, autI_nS hV hS hTM]
  exact hF.card_fix

end SubFacts

section Rank

variable {G : Type} [Group G] [Finite G]

theorem card_le_sq_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A) {τ : G}
    (hτN : τ ∈ Subgroup.normalizer (A : Set G)) (hτ2 : τ * τ ∈ Subgroup.centralizer (A : Set G)) :
    Nat.card A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ^ 2 := by
  have hcomm : ∀ a b : A, a * b = b * a := hA.1.is_comm.comm
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  have hsq : ∀ a : A, a * a = 1 := fun a => by
    have := hA.2 a a.2
    exact Subtype.ext (by simpa [pow_two] using this)
  let c : A → A := fun a => ⟨τ * a * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτN a).mp a.2⟩
  have hc_val : ∀ a : A, ((c a : A) : G) = τ * a * τ⁻¹ := fun a => rfl
  have hc_mul : ∀ a b : A, c (a * b) = c a * c b := fun a b => Subtype.ext (by
    rw [hc_val, Subgroup.coe_mul, Subgroup.coe_mul, hc_val, hc_val]; group)
  have hc_inv : ∀ a : A, c a⁻¹ = (c a)⁻¹ := fun a => Subtype.ext (by
    rw [hc_val, Subgroup.coe_inv, Subgroup.coe_inv, hc_val]; group)
  have hcc : ∀ a : A, c (c a) = a := fun a => Subtype.ext (by
    rw [hc_val, hc_val]
    have h1 := Subgroup.mem_centralizer_iff.mp hτ2 (a : G) a.2
    calc τ * (τ * (a : G) * τ⁻¹) * τ⁻¹ = (τ * τ) * a * (τ * τ)⁻¹ := by group
      _ = a := by rw [← h1]; group)
  let φ : A →* A := MonoidHom.mk' (fun a => a⁻¹ * c a) (fun a b => by
    rw [hc_mul, mul_inv_rev]
    ac_rfl)
  have hφ : ∀ a : A, φ a = a⁻¹ * c a := fun a => rfl
  have hker : ∀ a : A, a ∈ φ.ker ↔ c a = a := fun a => by
    rw [MonoidHom.mem_ker, hφ, inv_mul_eq_one]
    exact eq_comm
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hrange : φ.range ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [hker, hφ, hc_mul, hc_inv, hcc, hinv, hinv]
    exact mul_comm _ _
  have hcard1 : Nat.card φ.ker * φ.ker.index = Nat.card A := Subgroup.card_mul_index _
  have hcard2 : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hle : Nat.card φ.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hrange
  have hker_le : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun a => (⟨((a : A) : G), Subgroup.mem_inf.2 ⟨(a : A).2, ?_⟩⟩ :
        ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)))) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have h1 : c (a : A) = (a : A) := (hker _).1 a.2
      have h2 : τ * ((a : A) : G) * τ⁻¹ = ((a : A) : G) := congrArg Subtype.val h1
      calc τ * ((a : A) : G) = (τ * ((a : A) : G) * τ⁻¹) * τ := by group
        _ = ((a : A) : G) * τ := by rw [h2]
    · intro a b hab
      have h1 : ((a : A) : G) = ((b : A) : G) := by
        have := congrArg (fun x : ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) => (x : G)) hab
        simpa using this
      exact Subtype.ext (Subtype.ext h1)
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := by rw [← hcard1, hcard2]
    _ ≤ Nat.card φ.ker * Nat.card φ.ker := Nat.mul_le_mul_left _ hle
    _ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({τ} : Set G)) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hker_le hker_le

end Rank


namespace Decomp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem relIndex_nS (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    (T ⊓ Subgroup.normalizer (V₁ : Set G)).relIndex T = 2 := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, -, -, -⟩ := D.model
  exact relIndex_nS_of_model hV hS h.T_le h.le_normalizer h.isSylowTwoOf_autI

theorem card_ZS (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    Nat.card ↥(VZ T M ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G)) = 4 := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, -, -, -⟩ := D.model
  exact card_ZS_of_model hV hS h.T_le h.le_normalizer h.isSylowTwoOf_autI

end Decomp153

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_8 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) =
        VZ T M ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) ∧
      Nat.card ↥(VZ T M ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G)) = 4 := by
  set S : Subgroup G := T ⊓ Subgroup.normalizer (V₁ : Set G) with hSdef
  set ZS : Subgroup G := VZ T M ⊓ Subgroup.centralizer (S : Set G) with hZSdef
  have hcard : Nat.card ZS = 4 := D.card_ZS h
  have hidx : S.relIndex T = 2 := D.relIndex_nS h
  have hST : S ≤ T := inf_le_left
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := h.lemma_15_3_2_two.2
  have hVS : VZ T M ≤ S := by
    refine le_inf h.VZ_le_T fun v hv => ?_
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h.elemAbelian.1.is_comm.comm ⟨x, D.le₁ hx⟩ ⟨v, hv⟩ |> congrArg Subtype.val
  have hZS_le : ZS ≤ omegaOneCenterOf S := fun v hv =>
    Subgroup.subset_closure ⟨⟨hVS hv.1, hv.2⟩, h.elemAbelian.2 v hv.1⟩
  obtain ⟨τ, hτT, hτS⟩ : ∃ τ ∈ T, τ ∉ S := by
    by_contra hcon
    push Not at hcon
    have : S = T := le_antisymm hST hcon
    rw [this, Subgroup.relIndex_self] at hidx
    omega
  have hSn : (S.subgroupOf T).index = 2 := hidx
  have hTN : T ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mp (Subgroup.normal_of_index_eq_two hSn)
  have hττS : τ * τ ∈ S := by
    have := Subgroup.mul_self_mem_of_index_two hSn (⟨τ, hτT⟩ : T)
    exact Subgroup.mem_subgroupOf.mp this
  have hτN₀ : τ ∈ Subgroup.normalizer (omegaOneCenterOf S : Set G) :=
    A4.normalizer_le_normalizer_omegaOneCenterOf S (hTN hτT)
  have hτ2 : τ * τ ∈ Subgroup.centralizer (omegaOneCenterOf S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (A4.centerOf_le_centralizer S (A4.omegaOneCenterOf_le_centerOf S hz)) (τ * τ) hττS).symm
  have hrank := card_le_sq_centralizer (B2F.isElemAbelian_omegaOneCenterOf S) hτN₀ hτ2
  have hcos : ∀ y ∈ T, y ∈ S ∨ y * τ⁻¹ ∈ S := fun y hy =>
    coset_of_relIndex_two hidx hy hτT hτS
  have hCZ : omegaOneCenterOf S ⊓ Subgroup.centralizer ({τ} : Set G) ≤
      quasithinOmegaOneCenter T := by
    rintro x ⟨hx0, hxτ⟩
    have hxc := A4.centerOf_le_centralizer S (A4.omegaOneCenterOf_le_centerOf S hx0)
    have hxS : x ∈ S := A4.omegaOneCenterOf_le S hx0
    have hxτ' : τ * x = x * τ := (Subgroup.mem_centralizer_iff.mp hxτ τ rfl)
    refine Subgroup.subset_closure ⟨⟨hST hxS, ?_⟩, A4.sq_eq_one_of_mem_omegaOneCenterOf hx0⟩
    show x ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hcos y hy with hyS | hyS
    · exact Subgroup.mem_centralizer_iff.mp hxc y hyS
    · have h1 := Subgroup.mem_centralizer_iff.mp hxc _ hyS
      calc y * x = (y * τ⁻¹) * (τ * x) := by group
        _ = (y * τ⁻¹) * (x * τ) := by rw [hxτ']
        _ = ((y * τ⁻¹) * x) * τ := by group
        _ = (x * (y * τ⁻¹)) * τ := by rw [h1]
        _ = x * y := by group
  have h2 : Nat.card ↥(omegaOneCenterOf S ⊓ Subgroup.centralizer ({τ} : Set G)) ≤ 2 := by
    rw [← hZ2]
    exact Subgroup.card_le_of_le hCZ
  have h4 : Nat.card ↥(omegaOneCenterOf S) ≤ 4 := by
    calc Nat.card ↥(omegaOneCenterOf S) ≤ Nat.card ↥(omegaOneCenterOf S ⊓
        Subgroup.centralizer ({τ} : Set G)) ^ 2 := hrank
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 4 := by norm_num
  have heq : ZS = omegaOneCenterOf S :=
    Subgroup.eq_of_le_of_card_ge hZS_le (by rw [hcard]; exact h4)
  exact ⟨heq.symm, hcard⟩

end Hyp153

end CFSG.Quasithin
