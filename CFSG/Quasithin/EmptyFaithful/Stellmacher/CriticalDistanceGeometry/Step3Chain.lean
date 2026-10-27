module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Vhat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Off15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Graph
public import CFSG.Quasithin.EmptyFaithful.SzF53MDict

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem eq_of_le_of_relIndex_eq_fin {A B K : Subgroup G} (h : A ≤ B) (hBK : B ≤ K)
    (he : A.relIndex K = B.relIndex K) : A = B := by
  have h1 := Subgroup.relIndex_mul_relIndex A B K h hBK
  have h2 : A.relIndex B = 1 := by
    have hne := relIndex_ne_zero' B K
    rw [he] at h1
    exact (Nat.mul_eq_right hne).mp h1
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp h2)

abbrev VhatData.img {γ : Geo H M} (V : VhatData γ) (X : Subgroup G) : Subgroup (Perm (Fin 5)) :=
  (X.subgroupOf (stab γ)).map V.ψ

theorem VhatData.card_img {γ : Geo H M} (V : VhatData γ) {X : Subgroup G} (hX : X ≤ stab γ) :
    Nat.card (V.img X) = (Qv γ).relIndex X :=
  card_map_subgroupOf_eq V.ψ V.ker hX

theorem VhatData.exp_img {γ : Geo H M} (V : VhatData γ) {X : Subgroup G} (hX : IsElemAbelian 2 X) :
    ∀ x ∈ V.img X, x * x = 1 := by
  rintro _ ⟨z, hz, rfl⟩
  have hz2 : (z : G) ^ 2 = 1 := isElemAbelian_pow_eq_one hX (Subgroup.mem_subgroupOf.mp hz)
  rw [← map_mul]
  have : z * z = 1 := Subtype.ext (by simpa [pow_two] using hz2)
  rw [this, map_one]

theorem psi_mem_alt_of_mem_oTwoRes {F : Subgroup G} (ψ : ↥F →* Perm (Fin 5)) {f : G}
    (hf : f ∈ oTwoRes F) : ∃ hfF : f ∈ F, ψ ⟨f, hfF⟩ ∈ alternatingGroup (Fin 5) := by
  have hle : oTwoRes F ≤ ((alternatingGroup (Fin 5)).comap ψ).map F.subtype := by
    rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hx, m, hm, hxm⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show ψ ⟨x, hx⟩ ∈ alternatingGroup (Fin 5)
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : Equiv.Perm.sign (ψ ⟨x, hx⟩) ^ m = 1 := by
      rw [← map_pow, ← map_pow]
      have : (⟨x, hx⟩ : ↥F) ^ m = 1 := Subtype.ext (by simpa using hxm)
      rw [this]; simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ψ ⟨x, hx⟩)) with h | h
    · exact h
    · rw [h, hm.neg_one_pow] at h1
      exact absurd h1 (by decide)
  obtain ⟨y, hy, rfl⟩ := hle hf
  exact ⟨y.2, hy⟩

omit [Finite G] in
theorem map_conj_subgroupOf_stab (F X : Subgroup G) (g : ↥F) :
    (X.subgroupOf F).map (MulAut.conj g).toMonoidHom = (conjSub (g : G) X).subgroupOf F := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_conjSub]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have := Subgroup.mem_subgroupOf.mp hz
    have e : (g : G)⁻¹ * (g * (z : G) * (g : G)⁻¹) * g = z := by group
    simpa [MulAut.conj_apply, e] using this
  · intro hyX
    refine ⟨g⁻¹ * y * g, Subgroup.mem_subgroupOf.mpr hyX, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem VhatData.map_conj_img {γ : Geo H M} (V : VhatData γ) (X : Subgroup G) (g : ↥(stab γ)) :
    (V.img X).map (MulAut.conj (V.ψ g)).toMonoidHom = V.img (conjSub (g : G) X) := by
  show _ = Subgroup.map V.ψ ((conjSub (g : G) X).subgroupOf (stab γ))
  rw [Subgroup.map_map, ← map_conj_subgroupOf_stab, Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply]

theorem alt_le_img_oTwoRes {F : Subgroup G} {θ : ↥F →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) :
    alternatingGroup (Fin 5) ≤ ((oTwoRes F).subgroupOf F).map θ := by
  have hthree : ∀ τ : Perm (Fin 5), τ.IsThreeCycle →
      ∃ o : G, o ∈ F ∧ (∃ m : ℕ, Odd m ∧ o ^ m = 1) ∧ ∃ ho : o ∈ F, θ ⟨o, ho⟩ = τ := by
    intro τ hτ
    obtain ⟨g, rfl⟩ := hθs τ
    have hg : IsOfFinOrder (g : G) := (isOfFinOrder_of_finite g.1)
    obtain ⟨j, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    have hτ3 : θ g ^ 3 = 1 := by
      rw [← pow_orderOf_eq_one (θ g), hτ.orderOf]
    refine ⟨(g : G) ^ (4 ^ j), F.pow_mem g.2 _, ⟨m', hm', ?_⟩, F.pow_mem g.2 _, ?_⟩
    · rw [← pow_mul]
      have : 4 ^ j * m' = 2 ^ j * m' * 2 ^ j := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
      rw [this, pow_mul, ← hm, pow_orderOf_eq_one, one_pow]
    · show θ (g ^ 4 ^ j) = θ g
      rw [map_pow]
      have h4 : ∀ t : ℕ, θ g ^ (4 ^ t) = θ g := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, pow_mul, ih]
          have : θ g ^ 4 = θ g := by
            rw [show 4 = 3 + 1 by norm_num, pow_add, hτ3, one_mul, pow_one]
          exact this
      exact h4 j
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro τ hτ
  obtain ⟨o, hoF, hodd, ho, hθo⟩ := hthree τ hτ
  exact ⟨⟨o, hoF⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨hoF, hodd⟩), hθo⟩

omit [Finite G] in
theorem fixSecIn_le_sec (A L N : Subgroup G) : fixSecIn A L N ≤ N :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

@[expose] def Ctilde (γ : Geo H M) : Subgroup G := fixSecIn (oTwoRes (stab γ)) (Zv γ) (Vn γ)

theorem VhatData.img_oTwoRes {γ : Geo H M} (V : VhatData γ) :
    V.img (oTwoRes (stab γ)) = alternatingGroup (Fin 5) := by
  refine le_antisymm ?_ (alt_le_img_oTwoRes V.surj)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hzF, hzA⟩ := psi_mem_alt_of_mem_oTwoRes V.ψ (Subgroup.mem_subgroupOf.mp hz)
  exact hzA

theorem VhatData.mem_fixW_alt_iff {γ : Geo H M} (V : VhatData γ) (hLX : Zv γ ≤ Vn γ)
    {u : V.M5.W} {x : ↥(Vn γ)} (hux : V.β u = QuotientGroup.mk x) :
    u ∈ fixW V.M5 (alternatingGroup (Fin 5)) ↔ (x : G) ∈ Ctilde γ := by
  have := V.norm
  rw [← V.img_oTwoRes]
  exact secData_mem_fixW_iff V.secData hLX (oTwoRes_le _) hux

namespace Step3Ctx
variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')
include C

theorem index_Wv_le_card (P : CritPath α β α') (V : VhatData P.γ) :
    (Wv α ⊓ stab α').relIndex (Wv α) ≤ Nat.card (V.img (Wv α)) := by
  have hb := C.hb6
  rw [V.card_img (C.Wv_le_stab_γ P), Subgroup.inf_relIndex_left]
  exact Subgroup.relIndex_le_of_le_left
    (Qv_le_stab_of_mem_nbrs C.hA (P.γ_adj (by omega))) (relIndex_ne_zero' _ _)

theorem chain_aux (P : CritPath α β α') (V : VhatData P.γ) :
    (fixW V.M5 (V.img (Wv α))).index = Nat.card (V.img (Wv α)) ∧
    (Wv α ⊓ stab α').relIndex (Wv α) = Nat.card (V.img (Wv α)) ∧
    (Vn P.γ ⊓ Vn P.ε).relIndex (Vn P.γ) = Nat.card (V.img (Wv α)) ∧
    Vn P.γ ⊓ Vn P.ε = Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G) ∧
    fixSecIn (Wv α) (Zv P.γ) (Vn P.γ) = Vn P.γ ⊓ Vn P.ε ∧
    (Nat.card (V.img (Wv α)) = 2 ∨ Nat.card (V.img (Wv α)) = 4) := by
  have hb := C.hb6
  have hWγ := C.Wv_le_stab_γ P
  have hLX : Zv P.γ ≤ Vn P.γ := Zv_le_Vn_self C.hA P.γ
  have := V.norm
  have ha := C.index_Wv_le_card P V
  have ha2 := C.two_le_index_Wv P
  have hD := C.Vn_index_le_γ_ε P
  have hDC : Vn P.γ ⊓ Vn P.ε ≤ Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G) := by
    refine inf_le_inf_left _ ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h := C.comm_Wv_Vn_ε P
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hw
    exact (Subgroup.mem_centralizer_iff.mp this x hx).symm
  have hCF : Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G) ≤ fixSecIn (Wv α) (Zv P.γ) (Vn P.γ) := by
    intro x hx
    refine Subgroup.subset_closure ⟨hx.1, fun a ha => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hx.2 a ha
    rw [this]
    simp
  have hFV : fixSecIn (Wv α) (Zv P.γ) (Vn P.γ) ≤ Vn P.γ := by
    intro x hx
    exact ((X1512.mem_fixSecIn hLX).mp hx).1
  have hCV : Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G) ≤ Vn P.γ := inf_le_left
  have hDV : Vn P.γ ⊓ Vn P.ε ≤ Vn P.γ := inf_le_left
  have e1 := V.secData.relIndex_fixSecIn hLX hWγ
  have i1 : (fixSecIn (Wv α) (Zv P.γ) (Vn P.γ)).relIndex (Vn P.γ) ≤
      (Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G)).relIndex (Vn P.γ) :=
    Subgroup.relIndex_le_of_le_left hCF (relIndex_ne_zero' _ _)
  have i2 : (Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G)).relIndex (Vn P.γ) ≤
      (Vn P.γ ⊓ Vn P.ε).relIndex (Vn P.γ) :=
    Subgroup.relIndex_le_of_le_left hDC (relIndex_ne_zero' _ _)
  have hne : V.img (Wv α) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at ha
    omega
  have hoff : (fixW V.M5 (V.img (Wv α))).index ≤ Nat.card (V.img (Wv α)) := by
    rw [← e1]; omega
  obtain ⟨⟨hidx, -, hc24⟩, -, -, -⟩ :=
    off15_of_faithful V.M5 V.faithful hne (V.exp_img (C.isElemAbelian_Wv α)) hoff
  rw [← e1] at hidx
  have hFC := eq_of_le_of_relIndex_eq_fin hCF hFV (by omega)
  have hDC' := eq_of_le_of_relIndex_eq_fin hDC hCV (by omega)
  refine ⟨by rw [← e1]; exact hidx, by omega, by omega, hDC', ?_, hc24⟩
  rw [← hFC, ← hDC']

theorem card_img_edge (P : CritPath α β α') (V : VhatData P.γ) :
    Nat.card (V.img (stab P.γ ⊓ stab P.δ)) = 8 := by
  have hb := C.hb6
  rw [V.card_img inf_le_left]
  exact relIndex_Qv_inf_false C.hA (mem_nbrs_comm (P.δ_adj (by omega)) : P.δ ∈ nbrs P.γ)
    (C.vtype_γ P)

theorem img_Wv_le_img_edge (P : CritPath α β α') (V : VhatData P.γ) :
    V.img (Wv α) ≤ V.img (stab P.γ ⊓ stab P.δ) :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr
    (le_inf (C.Wv_le_stab_γ P) (C.Wv_le_stab_δ P) (Subgroup.mem_subgroupOf.mp hx))

theorem card_img_Wv (P : CritPath α β α') (V : VhatData P.γ) : Nat.card (V.img (Wv α)) = 4 := by
  have hb := C.hb6
  obtain ⟨hidx, ha, -, -, hFD, -⟩ := C.chain_aux P V
  have ha2 := C.two_le_index_Wv P
  have hLX : Zv P.γ ≤ Vn P.γ := Zv_le_Vn_self C.hA P.γ
  have := V.norm
  have hne : V.img (Wv α) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at ha
    omega
  refine off15_card_four_of_inv V.M5 (fixW_alt5_ne_top_of_faithful V.faithful)
    (C.card_img_edge P V) (C.img_Wv_le_img_edge P V) hne (V.exp_img (C.isElemAbelian_Wv α))
    hidx.le ?_
  refine secData_isInvSub_fixW V.secData hLX (C.Wv_le_stab_γ P) fun k hk x hx => ?_
  rw [hFD] at hx ⊢
  exact (Subgroup.mem_normalizer_iff.mp (C.inter_Vn_normal P hk) x).mp hx

theorem Wv_inf_stab_eq (P : CritPath α β α') (V : VhatData P.γ) :
    Wv α ⊓ stab α' = Wv α ⊓ Qv P.γ := by
  have hb := C.hb6
  obtain ⟨-, ha, -⟩ := C.chain_aux P V
  have hle : Wv α ⊓ Qv P.γ ≤ Wv α ⊓ stab α' :=
    inf_le_inf_left _ (Qv_le_stab_of_mem_nbrs C.hA (P.γ_adj (by omega)))
  refine (eq_of_le_of_relIndex_eq_fin hle inf_le_left ?_).symm
  rw [ha, V.card_img (C.Wv_le_stab_γ P), Subgroup.inf_relIndex_left]

theorem img_regular (P : CritPath α β α') (V : VhatData P.γ) :
    V.img (Wv α) ⊓ V.img (stab P.γ ⊓ stab α') = ⊥ := by
  have hb := C.hb6
  rw [eq_bot_iff]
  rintro _ ⟨⟨w, hw, rfl⟩, ⟨y, hy, hyw⟩⟩
  have hw' : (w : G) ∈ Wv α := Subgroup.mem_subgroupOf.mp hw
  have hy' : (y : G) ∈ stab P.γ ⊓ stab α' := Subgroup.mem_subgroupOf.mp hy
  have h1 : V.ψ (w * y⁻¹) = 1 := by rw [map_mul, map_inv, ← hyw, mul_inv_cancel]
  have h2 : ((w * y⁻¹ : ↥(stab P.γ)) : G) ∈ Qv P.γ := (V.ker _).mp h1
  have h3 : ((w * y⁻¹ : ↥(stab P.γ)) : G) ∈ stab α' :=
    Qv_le_stab_of_mem_nbrs C.hA (P.γ_adj (by omega)) h2
  have hwα : (w : G) ∈ stab α' := by
    have := Subgroup.mul_mem _ h3 hy'.2
    simpa using this
  have hwQ : (w : G) ∈ Qv P.γ := by
    have : (w : G) ∈ Wv α ⊓ stab α' := ⟨hw', hwα⟩
    rw [C.Wv_inf_stab_eq P V] at this
    exact this.2
  exact (V.ker w).mpr hwQ

theorem alt_le_img_sup (P : CritPath α β α') (V : VhatData P.γ) {g : ↥(H ⊔ M)}
    (hgγ : g • P.γ = P.γ) (hgδ : g • P.δ = α') :
    alternatingGroup (Fin 5) ≤ V.img (Wv α) ⊔ V.img (conjSub (g : G) (Wv α)) := by
  have hg : (g : G) ∈ stab P.γ := mem_stab_of_smul_eq hgγ
  set g' : ↥(stab P.γ) := ⟨g, hg⟩ with hg'
  have hedge : conjSub (g : G) (stab P.γ ⊓ stab P.δ) = stab P.γ ⊓ stab α' := by
    have e1 := stab_smul g P.γ
    have e2 := stab_smul g P.δ
    rw [hgγ] at e1
    rw [hgδ] at e2
    rw [conjSub_inf, ← e1, ← e2]
  have hreg : V.img (Wv α) ⊓ (V.img (stab P.γ ⊓ stab P.δ)).map (MulAut.conj (V.ψ g')).toMonoidHom
      = ⊥ := by
    rw [V.map_conj_img, hedge]
    exact C.img_regular P V
  obtain ⟨h1, h2⟩ := p13 (C.card_img_edge P V) (C.img_Wv_le_img_edge P V)
    (V.exp_img (C.isElemAbelian_Wv α)) (C.card_img_Wv P V) hreg
  rw [V.map_conj_img] at h1 h2
  by_cases hB : V.img (Wv α) ≤ alternatingGroup (Fin 5)
  · exact (h1 hB).ge
  · exact fun x _ => (h2 hB).symm ▸ Subgroup.mem_top x

theorem oTwoRes_le_sup (P : CritPath α β α') (V : VhatData P.γ) {g : ↥(H ⊔ M)}
    (hgγ : g • P.γ = P.γ) (hgδ : g • P.δ = α') :
    oTwoRes (stab P.γ) ≤ (Wv α ⊔ conjSub (g : G) (Wv α)) ⊔ Qv P.γ := by
  have hA := C.alt_le_img_sup P V hgγ hgδ
  have hsub : V.img (Wv α) ⊔ V.img (conjSub (g : G) (Wv α)) ≤
      V.img (Wv α ⊔ conjSub (g : G) (Wv α)) :=
    sup_le (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
      (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
  intro f hf
  obtain ⟨hfF, hfA⟩ := psi_mem_alt_of_mem_oTwoRes V.ψ hf
  obtain ⟨x, hx, hxf⟩ := hsub (hA hfA)
  have hq : ((x⁻¹ * ⟨f, hfF⟩ : ↥(stab P.γ)) : G) ∈ Qv P.γ :=
    (V.ker _).mp (by rw [map_mul, map_inv, hxf]; simp)
  have e : f = (x : G) * ((x⁻¹ * ⟨f, hfF⟩ : ↥(stab P.γ)) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hx) hq

theorem Zv_le_Ctilde (γ : Geo H M) : Zv γ ≤ Ctilde γ := by
  intro z hz
  refine Subgroup.subset_closure ⟨Zv_le_Vn_self C.hA γ hz, fun a ha => ?_⟩
  have h := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA γ (oTwoRes_le _ ha)) z).mp hz
  exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hz)

theorem Ctilde_normal (γ : Geo H M) : stab γ ≤ Subgroup.normalizer (Ctilde γ : Set G) := by
  have := (C.isSec_Vn γ).normal_subgroupOf
  have hLX := Zv_le_Vn_self C.hA γ
  refine le_normalizer_of_conj_mem fun x hx c hc => ?_
  rw [Ctilde, X1512.mem_fixSecIn hLX] at hc ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn γ hx) c).mp hc.1,
    fun a ha => ?_⟩
  have ha' : x⁻¹ * a * x ∈ oTwoRes (stab γ) := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (stab γ) (Subgroup.inv_mem _ hx))
      a).mp ha
    simpa using this
  have h1 := hc.2 _ ha'
  have h2 := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA γ hx) _).mp h1
  have e : x * ((x⁻¹ * a * x) * c * (x⁻¹ * a * x)⁻¹ * c⁻¹) * x⁻¹ =
      a * (x * c * x⁻¹) * a⁻¹ * (x * c * x⁻¹)⁻¹ := by group
  rwa [e] at h2

theorem off15_Wv (P : CritPath α β α') (V : VhatData P.γ) :
    ((fixW V.M5 (V.img (Wv α))).index = Nat.card (V.img (Wv α)) ∧
        (fixW V.M5.modA5 (V.img (Wv α))).index = Nat.card (V.img (Wv α)) ∧
        (Nat.card (V.img (Wv α)) = 2 ∨ Nat.card (V.img (Wv α)) = 4)) ∧
      fixW V.M5 (alternatingGroup (Fin 5)) ≤ fixW V.M5 (V.img (Wv α)) ∧
      (∀ x : V.M5.W, V.M5.projA5 x ∈ fixW V.M5.modA5 (V.img (Wv α)) →
        x ∈ fixW V.M5 (V.img (Wv α))) ∧
      ((Nonempty (V.M5.modA5.Iso orth) ∧
          ((∃ t : Perm (Fin 5), t.IsSwap ∧ V.img (Wv α) = Subgroup.zpowers t) ∨
            (Nat.card (V.img (Wv α)) = 4 ∧ ¬ V.img (Wv α) ≤ alternatingGroup (Fin 5)))) ∨
        (Nonempty (V.M5.modA5.Iso nat) ∧ Nat.card (V.img (Wv α)) = 4 ∧
          V.img (Wv α) ≤ alternatingGroup (Fin 5))) := by
  obtain ⟨hidx, ha, -⟩ := C.chain_aux P V
  have ha2 := C.two_le_index_Wv P
  have hne : V.img (Wv α) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at ha
    omega
  exact off15_of_faithful V.M5 V.faithful hne (V.exp_img (C.isElemAbelian_Wv α)) hidx.le

theorem vhat_orth_or_nat (P : CritPath α β α') (V : VhatData P.γ) :
    (Nonempty (V.M5.modA5.Iso orth) ∧ ¬ V.img (Wv α) ≤ alternatingGroup (Fin 5)) ∨
      (Nonempty (V.M5.modA5.Iso nat) ∧ V.img (Wv α) ≤ alternatingGroup (Fin 5)) := by
  have h4 := C.card_img_Wv P V
  obtain ⟨-, -, -, hcases⟩ := C.off15_Wv P V
  rcases hcases with ⟨hi, ⟨t, ht, hB⟩ | ⟨-, hA⟩⟩ | ⟨hi, -, hA⟩
  · exfalso
    rw [hB, Nat.card_zpowers, ht.orderOf] at h4
    omega
  · exact Or.inl ⟨hi, hA⟩
  · exact Or.inr ⟨hi, hA⟩

theorem Ctilde_le_inter (P : CritPath α β α') (V : VhatData P.γ) :
    Ctilde P.γ ≤ Vn P.γ ⊓ Vn P.ε := by
  have hLX := Zv_le_Vn_self C.hA P.γ
  have := V.norm
  obtain ⟨-, hAB, -, -⟩ := C.off15_Wv P V
  obtain ⟨-, -, -, -, hFD, -⟩ := C.chain_aux P V
  intro x hx
  have hxV : x ∈ Vn P.γ := fixSecIn_le_sec _ _ _ hx
  obtain ⟨u, hu⟩ := V.secData.surj (QuotientGroup.mk (⟨x, hxV⟩ : ↥(Vn P.γ)))
  have h1 : u ∈ fixW V.M5 (alternatingGroup (Fin 5)) :=
    (V.mem_fixW_alt_iff hLX hu).mpr hx
  have h2 := (secData_mem_fixW_iff V.secData hLX (C.Wv_le_stab_γ P) hu).mp (hAB h1)
  rwa [hFD] at h2

theorem chain (P : CritPath α β α') (V : VhatData P.γ) :
    Nat.card (V.img (Wv α)) = 4 ∧
    (Wv α ⊓ stab α').relIndex (Wv α) = 4 ∧
    Wv α ⊓ stab α' = Wv α ⊓ Qv P.γ ∧
    (Vn P.γ ⊓ Vn P.ε).relIndex (Vn P.γ) = 4 ∧
    Vn P.γ ⊓ Vn P.ε = Vn P.γ ⊓ Subgroup.centralizer (Wv α : Set G) ∧
    fixSecIn (Wv α) (Zv P.γ) (Vn P.γ) = Vn P.γ ⊓ Vn P.ε ∧
    (fixW V.M5 (V.img (Wv α))).index = 4 := by
  have h4 := C.card_img_Wv P V
  obtain ⟨hidx, ha, hD, hDC, hFD, -⟩ := C.chain_aux P V
  exact ⟨h4, h4 ▸ ha, C.Wv_inf_stab_eq P V, h4 ▸ hD, hDC, hFD, h4 ▸ hidx⟩

noncomputable def vhatData (P : CritPath α β α') : VhatData P.γ :=
  (C.nonempty_vhatData (C.vtype_γ P)).some

end Step3Ctx

namespace CritPath

variable {α β α' : Geo H M} (P : CritPath α β α')

theorem reverse_γ (hb : 1 ≤ bMin H M) : P.reverse.γ = β := by
  show P.p (bMin H M - (bMin H M - 1)) = β
  rw [show bMin H M - (bMin H M - 1) = 1 by omega, P.p_one]

theorem reverse_ε (hb : 3 ≤ bMin H M) : P.reverse.ε = P.p 3 := by
  show P.p (bMin H M - (bMin H M - 3)) = P.p 3
  rw [show bMin H M - (bMin H M - 3) = 3 by omega]

end CritPath

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem chain_symm (P : CritPath α β α') (V : VhatData β) :
    Nat.card (V.img (Wv α')) = 4 ∧
    (Wv α' ⊓ stab α).relIndex (Wv α') = 4 ∧
    Wv α' ⊓ stab α = Wv α' ⊓ Qv β ∧
    (Vn β ⊓ Vn (P.p 3)).relIndex (Vn β) = 4 ∧
    Vn β ⊓ Vn (P.p 3) = Vn β ⊓ Subgroup.centralizer (Wv α' : Set G) ∧
    fixSecIn (Wv α') (Zv β) (Vn β) = Vn β ⊓ Vn (P.p 3) ∧
    (fixW V.M5 (V.img (Wv α'))).index = 4 := by
  have hb := C.hb6
  have key : ∀ (γ ε : Geo H M), P.reverse.γ = γ → P.reverse.ε = ε → ∀ V : VhatData γ,
      Nat.card (V.img (Wv α')) = 4 ∧
      (Wv α' ⊓ stab α).relIndex (Wv α') = 4 ∧
      Wv α' ⊓ stab α = Wv α' ⊓ Qv γ ∧
      (Vn γ ⊓ Vn ε).relIndex (Vn γ) = 4 ∧
      Vn γ ⊓ Vn ε = Vn γ ⊓ Subgroup.centralizer (Wv α' : Set G) ∧
      fixSecIn (Wv α') (Zv γ) (Vn γ) = Vn γ ⊓ Vn ε ∧
      (fixW V.M5 (V.img (Wv α'))).index = 4 := by
    rintro γ ε rfl rfl V
    exact (C.symm P).chain P.reverse V
  exact key β (P.p 3) (P.reverse_γ (by omega)) (P.reverse_ε (by omega)) V

theorem vhat_orth_or_nat_symm (P : CritPath α β α') (V : VhatData β) :
    (Nonempty (V.M5.modA5.Iso orth) ∧ ¬ V.img (Wv α') ≤ alternatingGroup (Fin 5)) ∨
      (Nonempty (V.M5.modA5.Iso nat) ∧ V.img (Wv α') ≤ alternatingGroup (Fin 5)) := by
  have hb := C.hb6
  have key : ∀ (γ : Geo H M), P.reverse.γ = γ → ∀ V : VhatData γ,
      (Nonempty (V.M5.modA5.Iso orth) ∧ ¬ V.img (Wv α') ≤ alternatingGroup (Fin 5)) ∨
      (Nonempty (V.M5.modA5.Iso nat) ∧ V.img (Wv α') ≤ alternatingGroup (Fin 5)) := by
    rintro γ rfl V
    exact (C.symm P).vhat_orth_or_nat P.reverse V
  exact key β (P.reverse_γ (by omega)) V

noncomputable def vhatDataBeta : VhatData β :=
  (C.nonempty_vhatData C.vtype_beta).some

end Step3Ctx

end F53.Stellmacher

end CFSG.Quasithin
