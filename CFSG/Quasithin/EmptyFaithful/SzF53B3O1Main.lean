module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1B6
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Tab
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Kern
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Gen
public import CFSG.Quasithin.EmptyFaithful.SzF53B3OrthDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53B3A6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53B3

namespace O1

variable {G : Type} [Group G]

theorem exists_odd_coset [Finite G] {F L X S₀ : Subgroup G} (h : IsOrthSec F L X)
    (hS : IsSylowTwoOf S₀ F) :
    ∃ s ∈ S₀, ∀ g ∈ F, g ∈ oTwoRes F ⊔ cSecIn F L X ∨ g * s⁻¹ ∈ oTwoRes F ⊔ cSecIn F L X := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hτ : Equiv.swap (0 : Fin 5) 2 ∈ S5Syl := Subgroup.subset_closure (Or.inr rfl)
  rw [← hPS] at hτ
  obtain ⟨s', hs', hΨs'⟩ := hτ
  refine ⟨s', Subgroup.mem_subgroupOf.mp hs', fun g hg => ?_⟩
  have hsF : (s' : G) ∈ F := s'.2
  by_cases hgA : θ ⟨g, hg⟩ ∈ alternatingGroup (Fin 5)
  · exact Or.inl ((mem_oTwoRes_sup_iff hθs hθk hg).mpr hgA)
  · right
    have hgs : g * (s' : G)⁻¹ ∈ F := F.mul_mem hg (F.inv_mem hsF)
    refine (mem_oTwoRes_sup_iff hθs hθk hgs).mpr ?_
    rw [Equiv.Perm.mem_alternatingGroup] at hgA ⊢
    have e : θ ⟨g * (s' : G)⁻¹, hgs⟩ = θ ⟨g, hg⟩ * (θ s')⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    have h1 : Equiv.Perm.sign (θ s') = -1 := by
      rw [← hsgn s', hΨs']
      exact Equiv.Perm.sign_swap (by decide)
    have h2 : Equiv.Perm.sign (θ ⟨g, hg⟩) = -1 := (Int.units_eq_one_or _).resolve_left hgA
    rw [e, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, h1, h2]
    decide

variable [Finite G] {H M S : Subgroup G}

theorem R_ne_Zv (hB : B3FactsO H M S) {μ x y : Geo H M} (hμ : vtype μ = true) (hxy : x ≠ y)
    (hx : (graph (H ⊔ M) H M).Adj μ x) (hy : (graph (H ⊔ M) H M).Adj μ y) :
    Vn x ⊓ Vn y ≠ Zv μ := by
  intro hR
  have hA := hB.amalgam
  have hBl := blockFactsO hB
  have hxf : vtype x = false := vtype_nbr_of_true hx hμ
  have hyf : vtype y = false := vtype_nbr_of_true hy hμ
  have hdist : dist x y = 2 := N37.dist_eq_two_of_nbrs hx hy hxy
  obtain ⟨u, huV, huQ⟩ := IsConcreteLE.not_le_iff_exists.mp (hBl.not_vn_le_qv x y hxf hdist)
  have huQμ : u ∈ Qv μ := vn_le_qv_of_dist hB.toB3Base (N37.dist_le_one_of_adj hx.symm) huV
  have huS : u ∈ stab μ ⊓ stab y :=
    ⟨N37.Qv_le_stab_self μ huQμ, Qv_le_stab_of_mem_nbrs hA hy huQμ⟩
  refine orth_not_comm_fixed (hB.orth y hyf) (quot_stab_five hA hyf)
    (N37.sylow_inf_stab hA hy.symm) huS huQ ?_
  intro v hv s hs
  have hz : u * v * u⁻¹ * v⁻¹ ∈ Zv μ := by
    rw [← hR]
    exact hBl.comm_vn_vn x y hdist (Subgroup.commutator_mem_commutator huV hv)
  have := comm_zv_mem hB.toB3Base hyf (show μ ∈ nbrs y from hy.symm) ⟨hs.2, hs.1⟩ hz
  exact N37.Zv_le_Cv hBl hyf this

theorem cv_eq_of_le (hB : B3FactsO H M S) {y μ : Geo H M} (hy : vtype y = false)
    (hμ : (graph (H ⊔ M) H M).Adj y μ) (hle : Zv μ ≤ ⁅Vn y, stab y⁆) : Cv y = Zv y := by
  have hA := hB.amalgam
  have hBl := blockFactsO hB
  have hq := quot_stab_five hA hy
  have horth := hB.orth y hy
  have hS := N37.sylow_inf_stab hA hμ
  have hFV : stab y ≤ Subgroup.normalizer (Vn y : Set G) := stab_le_normalizer_Vn y
  have hFZ := stab_le_normalizer_Zv hA y
  have hZC : Zv y ≤ Cv y := N37.Zv_le_Cv hBl hy
  have hCV : Cv y ≤ Vn y := N37.Cv_le_Vn y
  have hcs : cSecIn (stab y) (Cv y) (Vn y) = Qv y := IsModelSec.cSecIn_eq_pCoreOf horth hq
  have hQ : ∀ q ∈ cSecIn (stab y) (Cv y) (Vn y), ∀ v ∈ Vn y, q * v * q⁻¹ * v⁻¹ ∈ Zv y := by
    intro q hq' v hv
    rw [hcs] at hq'
    have h1 : ⁅v, q⁆ ∈ ⁅Vn y, Qv y⁆ := Subgroup.commutator_mem_commutator hv hq'
    rw [hBl.comm_vn_qv y hy] at h1
    have e : q * v * q⁻¹ * v⁻¹ = (⁅v, q⁆)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Zv y).inv_mem h1
  have hcent : ∀ g ∈ stab y, ∀ z ∈ Zv y, g * z * g⁻¹ = z := fun g hg z hz =>
    conj_eq_of_central hB.toB3Base hy hg hz
  have hC : ∀ g ∈ oTwoRes (stab y) ⊔ cSecIn (stab y) (Cv y) (Vn y), ∀ c ∈ Cv y,
      g * c * g⁻¹ * c⁻¹ ∈ Zv y := by
    let T : Subgroup G :=
      { carrier := {g | g ∈ stab y ∧ ∀ c ∈ Cv y, g * c * g⁻¹ * c⁻¹ ∈ Zv y}
        one_mem' := ⟨(stab y).one_mem, fun c _ => by simp⟩
        mul_mem' := fun {a b} ha hb => by
          refine ⟨(stab y).mul_mem ha.1 hb.1, fun c hc => ?_⟩
          have e : a * b * c * (a * b)⁻¹ * c⁻¹ =
              (a * (b * c * b⁻¹ * c⁻¹) * a⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group
          rw [e, hcent a ha.1 _ (hb.2 c hc)]
          exact (Zv y).mul_mem (hb.2 c hc) (ha.2 c hc)
        inv_mem' := fun {a} ha => by
          refine ⟨(stab y).inv_mem ha.1, fun c hc => ?_⟩
          have e : a⁻¹ * c * a⁻¹⁻¹ * c⁻¹ = a⁻¹ * (a * c * a⁻¹ * c⁻¹)⁻¹ * a⁻¹⁻¹ := by group
          rw [e, hcent a⁻¹ ((stab y).inv_mem ha.1) _ ((Zv y).inv_mem (ha.2 c hc))]
          exact (Zv y).inv_mem (ha.2 c hc) }
    have hL : oTwoRes (stab y) ≤ T := by
      intro g hg
      refine ⟨oTwoRes_le _ hg, fun c hc => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hc.2 g hg
      have e : g * c * g⁻¹ * c⁻¹ = 1 := by rw [this]; group
      rw [e]
      exact (Zv y).one_mem
    have hQT : cSecIn (stab y) (Cv y) (Vn y) ≤ T := by
      intro g hg
      have hg' := hg
      rw [hcs] at hg'
      refine ⟨N37.Qv_le_stab_self y hg', fun c hc => ?_⟩
      have h1 := hQ g hg c (hCV hc)
      exact h1
    exact fun g hg => (sup_le hL hQT hg).2
  obtain ⟨s, hsS, hcos⟩ := exists_odd_coset horth hS
  have hCsF : cSecIn (stab y) (Cv y) (Vn y) ≤ stab y :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hFpF : oTwoRes (stab y) ⊔ cSecIn (stab y) (Cv y) (Vn y) ≤ stab y :=
    sup_le (oTwoRes_le _) hCsF
  have hFpn : ∀ g ∈ stab y, ∀ f ∈ oTwoRes (stab y) ⊔ cSecIn (stab y) (Cv y) (Vn y),
      g * f * g⁻¹ ∈ oTwoRes (stab y) ⊔ cSecIn (stab y) (Cv y) (Vn y) := by
    intro g hg
    refine conj_mem_sup (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (stab y) hg) a).mp ha)
    · rw [hcs] at hb
      refine Subgroup.mem_sup_right ?_
      rw [hcs]
      exact (Subgroup.mem_normalizer_iff.mp (N37.stab_le_normalizer_Qv y hg) b).mp hb
  have hVc : ∀ a ∈ Vn y, ∀ b ∈ Vn y, a * b = b * a := fun a ha b hb =>
    mul_comm_of_elemAbelian (hBl.elemAbelian_vn y) ha hb
  have hsZ : ∀ z ∈ Zv μ, s * z * s⁻¹ * z⁻¹ ∈ Zv y := fun z hz =>
    comm_zv_mem hB.toB3Base hy (show μ ∈ nbrs y from hμ) ⟨hsS.2, hsS.1⟩ hz
  have hV : ∀ N : Subgroup G, (∀ g ∈ stab y, ∀ z ∈ Zv μ, g * z * g⁻¹ ∈ N) → Vn y ≤ N := by
    intro N hN
    refine iSup₂_le fun κ hκ => ?_
    obtain ⟨g, hg, hgμ⟩ := stab_transitive_on_nbrs (show μ ∈ nbrs y from hμ) hκ
    intro z hz
    have h1 : z ∈ Zv (g • μ) := by rw [hgμ]; exact hz
    rw [Zv_smul, mem_conjSub] at h1
    have := hN g hg _ h1
    simpa [mul_assoc] using this
  have hgen := gen_of_comm hFpF hFpn hFV hFZ (hZC.trans hCV) (N37.Zv_le_Vn_of_adj hμ) hVc hsS.2
    hcos hsZ hV hle
  exact le_antisymm (eq_of_orth_kernel (hBl.elemAbelian_vn y) hFV hFZ hZC hCV horth hC hQ hgen) hZC

theorem cv_eq (hB : B3FactsO H M S) {y : Geo H M} (hy : vtype y = false) : Cv y = Zv y := by
  have hA := hB.amalgam
  obtain ⟨μ, x, hyμ, hμx, hxy, hμt, hxf, hdist⟩ := N37.exists_arc hA hy
  have hμy : (graph (H ⊔ M) H M).Adj μ y := hyμ.symm
  have hZ : Zv μ ≤ ⁅Vn x ⊓ Vn y, Qv μ⁆ :=
    (b6 hB.toB3Base hμt hxy hμx hμy).resolve_left (R_ne_Zv hB hμt hxy hμx hμy)
  exact cv_eq_of_le hB hy hyμ
    (hZ.trans (Subgroup.commutator_mono inf_le_right (Qv_le_stab_of_mem_nbrs hA hμy)))

theorem zv_le_comm (hB : B3FactsO H M S) {μ x y : Geo H M} (hμ : vtype μ = true) (hxy : x ≠ y)
    (hx : (graph (H ⊔ M) H M).Adj μ x) (hy : (graph (H ⊔ M) H M).Adj μ y) :
    Zv μ ≤ ⁅Vn x ⊓ Vn y, Qv μ⁆ :=
  (b6 hB.toB3Base hμ hxy hx hy).resolve_left (R_ne_Zv hB hμ hxy hx hy)

theorem card_R (hB : B3FactsO H M S) {μ x y : Geo H M} (hμ : vtype μ = true) (hxy : x ≠ y)
    (hx : (graph (H ⊔ M) H M).Adj μ x) (hy : (graph (H ⊔ M) H M).Adj μ y) :
    Nat.card ↥(Vn x ⊓ Vn y) = 8 := by
  have hA := hB.amalgam
  have hBl := blockFactsO hB
  have hxf : vtype x = false := vtype_nbr_of_true hx hμ
  have hyf : vtype y = false := vtype_nbr_of_true hy hμ
  have hdist : dist x y = 2 := N37.dist_eq_two_of_nbrs hx hy hxy
  have hcard32 : ∀ w : Geo H M, vtype w = false → Nat.card (Vn w) = 32 := by
    intro w hw
    have h1 := Subgroup.relIndex_mul_card (Cv w) (Vn w)
    have hc2 : Nat.card (Cv w) = 2 := by rw [cv_eq hB hw]; exact hB.card_two w hw
    rw [inf_of_le_left (N37.Cv_le_Vn w), hc2, (hB.orth w hw).relIndex_eq] at h1
    omega
  set R := Vn x ⊓ Vn y with hR
  have hZR : Zv μ ≤ R := le_inf (N37.Zv_le_Vn_of_adj hx.symm) (N37.Zv_le_Vn_of_adj hy.symm)
  have hdvd4 : 4 ∣ Nat.card R := by
    have := Subgroup.card_dvd_of_le hZR
    rwa [card_zv_true hB.toB3Base hμ] at this
  have hdvd32 : Nat.card R ∣ 32 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : R ≤ Vn y)
    rwa [hcard32 y hyf] at this
  have hne4 : Nat.card R ≠ 4 := by
    intro h4
    apply R_ne_Zv hB hμ hxy hx hy
    exact (Subgroup.eq_of_le_of_card_ge hZR (by rw [card_zv_true hB.toB3Base hμ, h4])).symm
  have hne32 : Nat.card R ≠ 32 := by
    intro h32
    have hRx : R = Vn x :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : R ≤ Vn x) (by rw [hcard32 x hxf, h32])
    have : Vn x ≤ Qv y := by
      rw [← hRx]
      exact (inf_le_right : R ≤ Vn y).trans (N37.Vn_le_Qv_self hBl y)
    exact hBl.not_vn_le_qv x y hxf hdist this
  have hne16 : Nat.card R ≠ 16 := by
    intro h16
    have hcy := cv_eq hB hyf
    have hZyR : Zv y ≤ R := (hBl.zv_le_zv y μ hyf hy.symm).trans hZR
    have hCyR : Cv y ≤ R := by rw [hcy]; exact hZyR
    have hR8 : (Cv y).relIndex R = 8 := by
      have h1 := Subgroup.relIndex_mul_card (Cv y) R
      have hc2 : Nat.card (Cv y) = 2 := by rw [hcy]; exact hB.card_two y hyf
      rw [inf_of_le_left hCyR, hc2, h16] at h1
      omega
    obtain ⟨u, huV, huQ⟩ := IsConcreteLE.not_le_iff_exists.mp (hBl.not_vn_le_qv x y hxf hdist)
    have huQμ : u ∈ Qv μ := vn_le_qv_of_dist hB.toB3Base (N37.dist_le_one_of_adj hx.symm) huV
    have huS : u ∈ stab μ ⊓ stab y :=
      ⟨N37.Qv_le_stab_self μ huQμ, Qv_le_stab_of_mem_nbrs hA hy huQμ⟩
    have hRn : stab μ ⊓ stab y ≤ Subgroup.normalizer (R : Set G) :=
      inf_le_left.trans (vn_inf_normal_of hB.toB3Base hxy.symm hμ hx hy)
    have hcomm : ∀ r ∈ R, u * r = r * u := fun r hr =>
      mul_comm_of_elemAbelian (hBl.elemAbelian_vn x) huV hr.1
    have hRV : R ≤ Vn y := inf_le_right
    have hVc : ∀ a ∈ Vn y, ∀ b ∈ Vn y, a * b = b * a := fun a ha b hb =>
      mul_comm_of_elemAbelian (hBl.elemAbelian_vn y) ha hb
    have hidx : (R.subgroupOf (Vn y)).index = 2 := by
      have h1 := (R.subgroupOf (Vn y)).card_mul_index
      have h2 : Nat.card (R.subgroupOf (Vn y)) = Nat.card R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv
      rw [h2, h16, hcard32 y hyf] at h1
      omega
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
    have hcA : u * (a : G) * u⁻¹ * (a : G)⁻¹ ∈ R :=
      hBl.comm_vn_vn x y hdist (Subgroup.commutator_mem_commutator huV a.2)
    have hrk : ∃ c ∈ Vn y, ∀ v ∈ Vn y, u * v * u⁻¹ * v⁻¹ ∈ Cv y ∨
        (u * v * u⁻¹ * v⁻¹) * c⁻¹ ∈ Cv y := by
      refine ⟨(u * (a : G) * u⁻¹ * (a : G)⁻¹)⁻¹, (Vn y).inv_mem (hRV hcA), fun v hv => ?_⟩
      by_cases hvR : v ∈ R
      · left
        have e : u * v * u⁻¹ * v⁻¹ = 1 := by rw [hcomm v hvR]; group
        rw [e]
        exact (Cv y).one_mem
      · right
        have hxor := ha ⟨v, hv⟩
        have hva : v * (a : G) ∈ R := by
          rcases hxor with ⟨h1, _⟩ | ⟨h1, h2⟩
          · exact Subgroup.mem_subgroupOf.mp h1
          · exact absurd (Subgroup.mem_subgroupOf.mp h1) hvR
        have hw : v * (u * (a : G) * u⁻¹ * (a : G)⁻¹) = (u * (a : G) * u⁻¹ * (a : G)⁻¹) * v :=
          hVc v hv _ (hRV hcA)
        have e1 : (u * v * u⁻¹ * v⁻¹) * (u * (a : G) * u⁻¹ * (a : G)⁻¹) =
            u * (v * (a : G)) * u⁻¹ * (v * (a : G))⁻¹ := by
          calc (u * v * u⁻¹ * v⁻¹) * (u * (a : G) * u⁻¹ * (a : G)⁻¹)
              = (u * v * u⁻¹ * v⁻¹) * (v * (u * (a : G) * u⁻¹ * (a : G)⁻¹) * v⁻¹) := by
                rw [hw]; group
            _ = u * (v * (a : G)) * u⁻¹ * (v * (a : G))⁻¹ := by group
        have e2 : u * (v * (a : G)) * u⁻¹ * (v * (a : G))⁻¹ = 1 := by
          rw [hcomm _ hva]; group
        have e3 : (u * v * u⁻¹ * v⁻¹) * (u * (a : G) * u⁻¹ * (a : G)⁻¹)⁻¹⁻¹ = 1 := by
          rw [inv_inv, e1, e2]
        rw [e3]
        exact (Cv y).one_mem
    exact orth_no_rank_one (hB.orth y hyf) (quot_stab_five hA hyf)
      (N37.sylow_inf_stab hA hy.symm) hCyR hRV hR8 hRn huS huQ hcomm hrk
  have hle : Nat.card R ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd32
  generalize Nat.card R = n at *
  interval_cases n <;> omega

end O1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem orthC1 (hB : B3FactsO H M S) : OrthC1 H M S where
  cv_eq := fun _ hβ => O1.cv_eq hB hβ
  card_R := fun _ _ _ hxy hμ hx hy => O1.card_R hB hμ hxy hx hy
  zv_le_comm := fun _ _ _ hxy hμ hx hy => O1.zv_le_comm hB hμ hxy hx hy

end F53B3

end CFSG.Quasithin
