module

public import CFSG.Quasithin.H13.L32NLem14325m

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

theorem exists_mem_sylow {H S C E : Subgroup G} (hS : QuasithinUnique.IsSylowTwoOf S H)
    (hCH : C ≤ H) (hC : H ≤ Subgroup.normalizer (C : Set G)) (hEH : E ≤ H)
    (hE : H ≤ Subgroup.normalizer (E : Set G)) (hsq : ∀ e ∈ E, e * e ∈ C) {e : G}
    (he : e ∈ E) : ∃ t ∈ S, t⁻¹ * e ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C' := C.subgroupOf H with hC'
  set E' := E.subgroupOf H with hE'
  have hC'n : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hC
  have hE'n : E'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).mpr hE
  have hsurj := QuotientGroup.mk'_surjective C'
  have hEbar : IsPGroup 2 (E'.map (QuotientGroup.mk' C')) := by
    rintro ⟨_, d, hd, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (QuotientGroup.mk' C' d) ^ 2 ^ 1 = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, pow_one, pow_two]
    exact Subgroup.mem_subgroupOf.mpr (hsq _ (Subgroup.mem_subgroupOf.mp hd))
  have hEbn : (E'.map (QuotientGroup.mk' C')).Normal := hE'n.map _ hsurj
  have hle := hEbar.le_sylow_of_normal (Sylow.mapSurjective hsurj (A4.toSylow hS))
  have hmem : QuotientGroup.mk' C' ⟨e, hEH he⟩ ∈
      ((Sylow.mapSurjective hsurj (A4.toSylow hS) : Sylow 2 _) : Subgroup (↥H ⧸ C')) :=
    hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he))
  rw [Sylow.coe_mapSurjective, A4.toSylow_coe] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  have hc : t⁻¹ * ⟨e, hEH he⟩ ∈ C' := QuotientGroup.eq.mp hte
  exact ⟨t, Subgroup.mem_subgroupOf.mp ht, Subgroup.mem_subgroupOf.mp hc⟩

abbrev cBar (T V : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod (nK T V g) (l32nH T V) (fsuU T V)

omit [Finite G] in
theorem H_le_normalizer_nK : l32nH T V ≤ Subgroup.normalizer (nK T V g : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => conj_mem_nK hh hn, fun hn => ?_⟩
  have h1 := conj_mem_nK ((l32nH T V).inv_mem hh) hn
  have e1 : h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n := by group
  rwa [e1] at h1

omit [Finite G] in
theorem H_le_normalizer_cBar : l32nH T V ≤ Subgroup.normalizer (cBar T V g : Set G) := by
  have key : ∀ {h c : G}, h ∈ l32nH T V → c ∈ cBar T V g → h * c * h⁻¹ ∈ cBar T V g := by
    intro h c hh hc
    obtain ⟨hcH, -, hcc⟩ := hc
    have hhcH : h * c * h⁻¹ ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem hh hcH) ((l32nH T V).inv_mem hh)
    refine ⟨hhcH, H_le_normalizer_nK hhcH, fun u hu => ?_⟩
    have hu' : h⁻¹ * u * h ∈ fsuU T V := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (L14332.l32nH_le_normalizer_fsuU T V ((l32nH T V).inv_mem hh)) u).mp hu
    have h1 := conj_mem_nK hh (hcc _ hu')
    have e1 : h * (c * (h⁻¹ * u * h) * c⁻¹ * (h⁻¹ * u * h)⁻¹) * h⁻¹ =
        h * c * h⁻¹ * u * (h * c * h⁻¹)⁻¹ * u⁻¹ := by group
    rwa [e1] at h1
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key hh hc, fun hc => ?_⟩
  have h1 := key ((l32nH T V).inv_mem hh) hc
  have e1 : h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c := by group
  rwa [e1] at h1

namespace CtxI

variable (C : CtxI G T L V V₂ g D)
include C

theorem T_V2 {t v : G} (ht : t ∈ T) (hv : v ∈ V₂) : t * v * t⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have hV₂ := C.ctx.plane
  have hidx : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr hV₂.2, C.ctx.card_V1, hV₂.1.2.1] at this
    omega
  have htH : t ∈ l32nH T V := C.ctx.T_le ht
  have htV₂ : t * v * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hV₂.1.2.2 ht) v).mp hv
  by_cases hv1 : v ∈ fsuV1 T V
  · rw [C.H_V1 htH hv1, mul_inv_cancel]
    exact one_mem _
  · have htv1 : t * v * t⁻¹ ∉ fsuV1 T V := fun h => hv1 (by
      have := C.H_V1 ((l32nH T V).inv_mem htH) h
      have e1 : t⁻¹ * (t * v * t⁻¹) * t⁻¹⁻¹ = v := by group
      rw [e1] at this
      rw [this]
      exact h)
    have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t * v * t⁻¹, htV₂⟩)
      (b := ⟨v⁻¹, V₂.inv_mem hv⟩)).mpr (iff_of_false
        (fun h => htv1 (Subgroup.mem_subgroupOf.mp h))
        (fun h => hv1 (by
          have := (fsuV1 T V).inv_mem (Subgroup.mem_subgroupOf.mp h)
          simpa using this)))
    exact Subgroup.mem_subgroupOf.mp hm

end CtxI

namespace CtxI.TransData

variable {C : CtxI G T L V V₂ g D} {x c : G} (X : TransData C x c)
include X

theorem cHat_zU (h64 : G64.LemmaG64) {e : G} (he : e ∈ l32nCHat T V) {w : G}
    (hw : w ∈ centerOf (fsuU T V)) : e * w * e⁻¹ * w⁻¹ ∈ nK T V g := by
  obtain ⟨v, hv, n, hn, rfl⟩ := X.exists_decomp h64 hw
  have hev : e * v * e⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp (X.cent_of_cHat h64 he) v hv
    calc e * v * e⁻¹ = v * e * e⁻¹ := by rw [this]
      _ = v := by group
  have hq : e * n * e⁻¹ * n⁻¹ ∈ nK T V g :=
    (nK T V g).mul_mem (conj_mem_nK he.1 hn) ((nK T V g).inv_mem hn)
  have hvq : v * (e * n * e⁻¹ * n⁻¹) = (e * n * e⁻¹ * n⁻¹) * v :=
    zU_comm (C.ctx.vH_le (X.vP_le hv)) hq.1
  have e1 : e * (v * n) * e⁻¹ * (v * n)⁻¹ = e * n * e⁻¹ * n⁻¹ := by
    calc e * (v * n) * e⁻¹ * (v * n)⁻¹ = (e * v * e⁻¹) * (e * n * e⁻¹ * n⁻¹) * v⁻¹ := by group
      _ = v * (e * n * e⁻¹ * n⁻¹) * v⁻¹ := by rw [hev]
      _ = (e * n * e⁻¹ * n⁻¹) * v * v⁻¹ := by rw [hvq]
      _ = e * n * e⁻¹ * n⁻¹ := by group
  rw [e1]
  exact hq

theorem sq_mem_cBar (h64 : G64.LemmaG64) {e : G} (he : e ∈ l32nCHat T V) :
    e * e ∈ cBar T V g := by
  have heH : e ∈ l32nH T V := he.1
  have hee : e * e ∈ l32nH T V := (l32nH T V).mul_mem heH heH
  refine ⟨hee, H_le_normalizer_nK hee, fun u hu => ?_⟩
  have hm : e * u * e⁻¹ * u⁻¹ ∈ centerOf (fsuU T V) := he.2.2 u hu
  have h1 := X.cHat_zU h64 he hm
  have h2 : (e * u * e⁻¹ * u⁻¹) * (e * u * e⁻¹ * u⁻¹) ∈ nK T V g := C.V1_le_nK (C.sq _ hm.1)
  have e1 : e * e * u * (e * e)⁻¹ * u⁻¹ =
      (e * (e * u * e⁻¹ * u⁻¹) * e⁻¹ * (e * u * e⁻¹ * u⁻¹)⁻¹) *
        ((e * u * e⁻¹ * u⁻¹) * (e * u * e⁻¹ * u⁻¹)) := by group
  rw [e1]
  exact (nK T V g).mul_mem h1 h2

theorem cHat_V2 (h64 : G64.LemmaG64) (hT : QuasithinUnique.IsSylowTwoOf T (l32nH T V))
    {e : G} (he : e ∈ l32nCHat T V) {v : G} (hv : v ∈ V₂) : e * v * e⁻¹ * v⁻¹ ∈ nK T V g := by
  obtain ⟨t, ht, htc⟩ := exists_mem_sylow hT (C := cBar T V g) (E := l32nCHat T V)
    (fun _ h => h.1) H_le_normalizer_cBar (fun _ h => h.1) le_normalizer_cHat
    (fun e he => X.sq_mem_cBar h64 he) he
  have hvU : v ∈ fsuU T V := C.ctx.V_U (C.ctx.plane.1.1 hv)
  have h1 : (t⁻¹ * e) * v * (t⁻¹ * e)⁻¹ * v⁻¹ ∈ nK T V g := htc.2.2 v hvU
  have h2 := conj_mem_nK (C.ctx.T_le ht) h1
  have h3 : t * v * t⁻¹ * v⁻¹ ∈ nK T V g := C.V1_le_nK (C.T_V2 ht hv)
  have e1 : e * v * e⁻¹ * v⁻¹ =
      t * ((t⁻¹ * e) * v * (t⁻¹ * e)⁻¹ * v⁻¹) * t⁻¹ * (t * v * t⁻¹ * v⁻¹) := by group
  rw [e1]
  exact (nK T V g).mul_mem h2 h3

theorem cHat_U (h64 : G64.LemmaG64) (hT : QuasithinUnique.IsSylowTwoOf T (l32nH T V))
    (hU : conjClosure V₂ (l32nH T V) = fsuU T V) {e : G} (he : e ∈ l32nCHat T V) {u : G}
    (hu : u ∈ fsuU T V) : e * u * e⁻¹ * u⁻¹ ∈ nK T V g := by
  have hUH : ∀ y ∈ conjClosure V₂ (l32nH T V), y ∈ l32nH T V := fun y hy =>
    C.ctx.U_le (hU ▸ hy)
  rw [← hU] at hu
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨h, hh, v, hv, rfl⟩ := hy
    have he' : h⁻¹ * e * h ∈ l32nCHat T V := by
      simpa using conj_mem_cHat ((l32nH T V).inv_mem hh) he
    have h2 := conj_mem_nK hh (X.cHat_V2 h64 hT he' hv)
    have e1 : e * (h * v * h⁻¹) * e⁻¹ * (h * v * h⁻¹)⁻¹ =
        h * ((h⁻¹ * e * h) * v * (h⁻¹ * e * h)⁻¹ * v⁻¹) * h⁻¹ := by group
    rw [e1]
    exact h2
  | one => simp
  | mul y y' hy hy' ih ih' =>
    have e1 : e * (y * y') * e⁻¹ * (y * y')⁻¹ =
        (e * y * e⁻¹ * y⁻¹) * (y * (e * y' * e⁻¹ * y'⁻¹) * y⁻¹) := by group
    rw [e1]
    exact (nK T V g).mul_mem ih (conj_mem_nK (hUH y hy) ih')
  | inv y hy ih =>
    have e1 : e * y⁻¹ * e⁻¹ * y⁻¹⁻¹ = y⁻¹ * (e * y * e⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e1]
    exact conj_mem_nK ((l32nH T V).inv_mem (hUH y hy)) ((nK T V g).inv_mem ih)

end CtxI.TransData

end L14325

end CFSG.Quasithin.H13
