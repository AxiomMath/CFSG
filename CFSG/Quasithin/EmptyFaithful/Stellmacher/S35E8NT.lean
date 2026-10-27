module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChLat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem psi_mem_alt_of_mem_oTwoRes' {F : Subgroup G} (ψ : ↥F →* Perm (Fin 5)) {f : G}
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

theorem oTwoRes_le_cSecIn_of_elt (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false)
    (c : Ch.Chart δ) {A U : Subgroup G} (hsec : IsSec (stab δ) A U) {x : G} (hxs : x ∈ stab δ)
    (hxQ : x ∉ Qv δ) (hx : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ A) :
    oTwoRes (stab δ) ≤ cSecIn (stab δ) A U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθk := c.ker_eq_Qv hS hδ
  have hθs := c.surj
  set θ := c.θ
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
    apply hxQ
    have hxK : x ∈ K := (hmemK x).mpr ⟨hxs, hx⟩
    have : θ ⟨x, hxs⟩ ∈ P := ⟨⟨x, hxs⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf] at this
    exact this
  have hAP := normal_ge_alt5 P hPne
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hys, m, hm, hym⟩
  obtain ⟨hys', hyA⟩ := psi_mem_alt_of_mem_oTwoRes' θ
    (Subgroup.subset_closure ⟨hys, m, hm, hym⟩ : y ∈ oTwoRes (stab δ))
  obtain ⟨k, hk, hky⟩ := hAP hyA
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  set q : ↥(stab δ) := k⁻¹ * ⟨y, hys⟩ with hq
  have hqQ : (q : G) ∈ Qv δ := by
    have : θ q = 1 := by rw [hq, map_mul, map_inv, hky, inv_mul_cancel]
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf] at this
    exact this
  have hykq : (⟨y, hys⟩ : ↥(stab δ)) = k * q := by rw [hq]; group
  have hck : hsec.conjHom k = 1 := hsec.conjHom_eq_one ((hmemK _).mp hkK).2
  have hcy : hsec.conjHom ⟨y, hys⟩ = hsec.conjHom q := by
    rw [hykq, map_mul, hck, one_mul]
  obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 (stab δ)) ⟨q, hqQ⟩
  have hqe : q ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
  have h1 : orderOf (hsec.conjHom ⟨y, hys⟩) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow]; rw [show (⟨y, hys⟩ : ↥(stab δ)) ^ m = 1 from
      Subtype.ext (by simpa using hym), map_one])
  have h2 : orderOf (hsec.conjHom ⟨y, hys⟩) ∣ 2 ^ e :=
    orderOf_dvd_of_pow_eq_one (by rw [hcy, ← map_pow, hqe, map_one])
  have hcop : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have h3 : orderOf (hsec.conjHom ⟨y, hys⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  refine (hmemK y).mpr ⟨hys, fun u hu => ?_⟩
  have key : ∀ v ∈ U, y * v⁻¹ * y⁻¹ * v ∈ A := by
    intro v hv
    have h4 := congrArg (fun φ => φ (hsec.proj ⟨v, hv⟩)) h3
    simp only [MulAut.one_apply] at h4
    have h5 : hsec.proj (hsec.conjN ⟨y, hys⟩ ⟨v, hv⟩) = hsec.proj ⟨v, hv⟩ := h4
    rw [hsec.proj_eq_proj_iff] at h5
    simpa [IsSec.conjN, mul_assoc] using h5
  simpa using key u⁻¹ (U.inv_mem hu)

omit [Finite G] in
theorem normalizer_of_comm {L N : Subgroup G} (hLN : L ≤ N)
    (hc : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ L) : N ≤ Subgroup.normalizer (L : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have key : ∀ w ∈ N, ∀ v ∈ L, w * v * w⁻¹ ∈ L := by
    intro w hw v hv
    have e : w * v * w⁻¹ = (w * v * w⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact L.mul_mem (hc w hw v (hLN hv)) hv
  refine ⟨fun hv => key w hw v hv, fun hv => ?_⟩
  have := key w⁻¹ (N.inv_mem hw) _ hv
  rwa [inv_inv, show w⁻¹ * (w * v * w⁻¹) * w = v by group] at this

theorem secIdx_ne_one (hS : Sit H M S) (hI : CaseI H M) (h6b : Claim6b H M) {β l : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hZ : IsOrthSec (stab β) (Zv β) (Vn β))
    (hsec : IsSec (stab β) (Vn β) (Wb β)) {x : G} (hxs : x ∈ stab β) (hxQ : x ∉ Qv β) :
    secIdx (Subgroup.zpowers x) (Vn β) (Wb β) ≠ 1 := by
  intro h1
  obtain ⟨c⟩ := Ch.nonempty_chart (Std.Zv_le_Vn_S5 hS hβ) hZ
  have hWL : Wb β ≤ Subgroup.normalizer (Vn β : Set G) :=
    normalizer_of_comm hsec.le hsec.comm
  have hxL : x ∈ Subgroup.normalizer (Vn β : Set G) := hsec.normL hxs
  have hfix : Wb β ≤ fixSecIn (Subgroup.zpowers x) (Vn β) (Wb β) := by
    unfold secIdx at h1
    exact Subgroup.relIndex_eq_one.mp h1
  have hx : ∀ u ∈ Wb β, x * u * x⁻¹ * u⁻¹ ∈ Vn β := fun u hu =>
    ((mem_fixSecIn_zpowers_iff hWL hxL).mp (hfix hu)).2
  have hL := oTwoRes_le_cSecIn_of_elt hS hβ c hsec hxs hxQ hx
  have hcomm : ⁅Wb β, Lr β⁆ ≤ Vn β := by
    rw [Subgroup.commutator_le]
    intro w hw g hg
    have h2 := ((mem_cSecIn_iff hsec.normL).mp (hL hg)).2 w hw
    rw [← commutatorElement_inv]
    refine (Vn β).inv_mem ?_
    rw [commutatorElement_def]
    exact h2
  obtain ⟨δ, δ', hδ, hδ', hδβ, -, -⟩ :=
    Std.exists_two_others hS (Std.vtype_nbr_S5 hβ hl) (Std.mem_nbrs_symm.mp hl)
  have h6 := h6b β l δ (Wb β) hβ hl (Std.mem_nbrs_symm.mp hδ) hδβ (Std.Wb_normal β)
    (Std.Vn_le_Wb_self hS hβ) le_rfl hcomm
  have hVδW : Vn δ ≤ Wb β := Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨l, hl, hδ, hδβ⟩)
  rw [inf_eq_left.mpr hVδW] at h6
  have hδ5 : vtype δ = false := Std.vtype_nbr_S3 (Std.vtype_nbr_S5 hβ hl) hδ
  obtain ⟨hc8, hc32⟩ := hI δ l β hδ5 (Std.mem_nbrs_symm.mp hδ) hl hδβ.symm
  rw [← h6, hc32] at hc8
  omega

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
