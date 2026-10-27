module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3bDict
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3bFin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

namespace C3b

theorem card_Zv_two_pow (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ∃ k : ℕ, Nat.card (Zv δ) = 2 ^ k := by
  have hp : IsPGroup 2 (Zv δ) := fun g => by
    refine ⟨1, ?_⟩
    have h := (isElemAbelian_Vn' hG δ).2 (g : G) (Zv_le_Vn hG hδ g.2)
    exact Subtype.ext (by simpa using h)
  exact (IsPGroup.iff_card).mp hp

namespace C3Data

variable {μ : Geo H M}

theorem card_Zv_le (D : C3Data δ μ) (hG : Glob H M S) (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    Nat.card (Zv δ) ≤ 4 := by
  rw [← D.card_Zbar hG hδ hμ]
  exact (Subgroup.card_le_of_le (D.Zbar_le_fixW hG hδ hμ)).trans
    (D.shape1.fix_le S5Syl card_S5Syl)

theorem card_Zv_ne_two (D : C3Data δ μ) (hG : Glob H M S) (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    Nat.card (Zv δ) ≠ 2 := by
  intro h2
  have hZ2 : Nat.card (D.Zbar hμ) = 2 := (D.card_Zbar hG hδ hμ).trans h2
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : ↥(D.Zbar hμ))).mp hZ2
  have hall : ∀ x ∈ D.Zbar hμ, x = 1 ∨ x = (y : D.mod.W) := by
    intro x hx
    by_cases h : (⟨x, hx⟩ : ↥(D.Zbar hμ)) = 1
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val (hyu _ h)
  set w : D.mod.W := y.1 with hw
  have hwfix : w ∈ fixW D.mod S4pt := by
    rw [← D.shape2.fix_S4]
    exact D.Zbar_le_fixW hG hδ hμ y.2
  set b : Fin 5 → D.mod.W := fun i => D.mod.act (swap i 4) w with hb
  set U := Subgroup.closure (Set.range b) with hU
  have hUinv : IsInvSub D.mod ⊤ U := by
    intro σ _ u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨(σ * swap i 4) 4, ?_⟩
      show D.mod.act (swap ((σ * swap i 4) 4) 4) w = D.mod.act σ (D.mod.act (swap i 4) w)
      rw [← act_eq_act_swap D.mod hwfix, ← act_mul_apply]
    | one => rw [map_one]; exact U.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact U.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact U.inv_mem hx
  have hw4 : w ∈ U := by
    refine Subgroup.subset_closure ⟨4, ?_⟩
    have h44 : swap (4 : Fin 5) 4 = 1 := Equiv.swap_self 4
    show D.mod.act (swap 4 4) w = w
    rw [h44, map_one]
    rfl
  have hZU : D.Zbar hμ ≤ U := by
    intro x hx
    rcases hall x hx with rfl | rfl
    · exact U.one_mem
    · exact hw4
  have htop := D.eq_top_of_Zbar_le hμ U hUinv hZU
  have hcard := card_closure_range_le (V := D.mod.W) D.mod.sq b
  have h8 := D.shape1.card
  rw [← hU, htop, Subgroup.card_top, h8] at hcard
  omega

end C3Data

end C3b

open C3b

theorem c3_card_Zv (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') : Nat.card (Zv δ) = 4 := by
  have hδ := hp.vδ
  obtain ⟨μ, hμ⟩ := exists_adj δ
  obtain ⟨D⟩ := nonempty_c3Data hG hirr h15 hng hp (show μ ∈ nbrs δ from hμ)
  have hle := D.card_Zv_le hG hδ hμ
  have hne := D.card_Zv_ne_two hG hδ hμ
  obtain ⟨k, hk⟩ := card_Zv_two_pow hG hδ
  have h1 : Nat.card (Zv δ) ≠ 1 := fun h =>
    Zv_ne_bot hG.amalg δ (Subgroup.card_eq_one.mp h)
  rw [hk] at hle hne h1 ⊢
  have hk2 : k ≤ 2 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

theorem c3_fix_eq (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') {μ : Geo H M} (hμ : μ ∈ nbrs δ) :
    fixSecIn (stab δ ⊓ stab μ) (Cb δ) (Vn δ) = Zv μ ⊔ Cb δ := by
  have hδ := hp.vδ
  obtain ⟨D⟩ := nonempty_c3Data hG hirr h15 hng hp hμ
  have h4 := c3_card_Zv hG hirr h15 hng hp
  have hA : stab δ ⊓ stab μ ≤ stab δ := inf_le_left
  have hZeq : D.Zbar hμ = fixW D.mod S5Syl := by
    refine Subgroup.eq_of_le_of_card_ge (D.Zbar_le_fixW hG hδ hμ) ?_
    rw [D.card_Zbar hG hδ hμ, h4]
    exact D.shape1.fix_le S5Syl card_S5Syl
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxf⟩ := (D.mem_fixSecIn_iff hA).mp hx
    rw [D.map_syl, ← hZeq] at hxf
    obtain ⟨z, hz, hzx⟩ := (D.mem_Zbar hμ).mp hxf
    have hc : z⁻¹ * x ∈ Cb δ := by
      have := (D.sec.proj_eq_proj_iff _ _).mp hzx
      simpa using this
    have : x = z * (z⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hz hc
  · refine sup_le (fun z hz => ?_) (fun x hx => ?_)
    · refine (D.mem_fixSecIn_iff hA).mpr ⟨Zv_le_Vn_nbr hμ hz, ?_⟩
      rw [D.map_syl]
      exact D.Zbar_le_fixW hG hδ hμ ((D.mem_Zbar hμ).mpr ⟨z, hz, rfl⟩)
    · have hxV : x ∈ Vn δ := Cb_le_Vn δ hx
      refine (D.mem_fixSecIn_iff hA).mpr ⟨hxV, ?_⟩
      rw [(D.sec.proj_eq_one_iff ⟨x, hxV⟩).mpr hx]
      exact Subgroup.one_mem _

omit [Finite G] in
theorem C3b.stab_inf_eq_conjSub {δ μ ν : Geo H M} {g : ↥(H ⊔ M)} (hgδ : (g : G) ∈ stab δ)
    (hgν : g • μ = ν) :
    stab δ ⊓ stab ν = conjSub (g : G) (stab δ ⊓ stab μ) := by
  have h1 : conjSub (g : G) (stab δ) = stab δ := by
    ext x
    rw [mem_conjSub]
    constructor
    · intro h
      have := (stab δ).mul_mem ((stab δ).mul_mem hgδ h) ((stab δ).inv_mem hgδ)
      simpa [mul_assoc] using this
    · intro h
      exact (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).inv_mem hgδ) h) hgδ
  rw [← hgν, stab_smul, conjSub_inf, h1]

theorem c3_fix_block (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') {μ ν : Geo H M} (hμ : μ ∈ nbrs δ) (hν : ν ∈ nbrs δ)
    (hb : SameBlock δ μ ν) :
    fixSecIn (stab δ ⊓ stab μ) (Cb δ) (Vn δ) = fixSecIn (stab δ ⊓ stab ν) (Cb δ) (Vn δ) := by
  obtain ⟨D⟩ := nonempty_c3Data hG hirr h15 hng hp hμ
  obtain ⟨P, hQP, hPS, hPne, hμP, hνP⟩ := hb
  have hAμ : stab δ ⊓ stab μ ≤ stab δ := inf_le_left
  have hAν : stab δ ⊓ stab ν ≤ stab δ := inf_le_left
  set R : Subgroup (Perm (Fin 5)) := (P.subgroupOf (stab δ)).map D.θ with hR
  have hSR : S5Syl ≤ R := by
    rw [← D.map_syl]
    exact Subgroup.map_mono (fun x hx => hμP hx)
  have hRtop : R ≠ ⊤ := by
    intro hRt
    apply hPne
    refine le_antisymm hPS (fun x hx => ?_)
    have hmem : D.θ ⟨x, hx⟩ ∈ R := by rw [hRt]; exact Subgroup.mem_top _
    obtain ⟨p, hp', hpx⟩ := hmem
    have hker : ((p⁻¹ * ⟨x, hx⟩ : ↥(stab δ)) : G) ∈ Qv δ :=
      (D.ker_iff _).mp (by rw [map_mul, map_inv, hpx, inv_mul_cancel])
    have hpP : (p : G) ∈ P := hp'
    have hx' : x = (p : G) * ((p⁻¹ * ⟨x, hx⟩ : ↥(stab δ)) : G) := by simp
    rw [hx']
    exact P.mul_mem hpP (hQP hker)
  have hRS4 := le_S4pt_of_syl_le hSR hRtop
  have hνS4 : ((stab δ ⊓ stab ν).subgroupOf (stab δ)).map D.θ ≤ S4pt :=
    (Subgroup.map_mono (show (stab δ ⊓ stab ν).subgroupOf (stab δ) ≤ P.subgroupOf (stab δ) from
      fun x hx => hνP hx)).trans hRS4
  have hle : fixW D.mod S5Syl ≤ fixW D.mod (((stab δ ⊓ stab ν).subgroupOf (stab δ)).map D.θ) := by
    rw [D.shape2.fix_S4]
    exact fixW_antitone D.mod hνS4
  obtain ⟨g, hgδ, hgν⟩ := stab_transitive_on_nbrs hμ hν
  have hAνeq := C3b.stab_inf_eq_conjSub hgδ hgν
  set gg : ↥(stab δ) := ⟨(g : G), hgδ⟩ with hgg
  have himg : ((stab δ ⊓ stab ν).subgroupOf (stab δ)).map D.θ =
      S5Syl.map (MulAut.conj (D.θ gg)).toMonoidHom := by
    ext σ
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ stab δ ⊓ stab ν := hy
      rw [hAνeq, mem_conjSub] at hy'
      refine ⟨D.θ (gg⁻¹ * y * gg), ?_, ?_⟩
      · rw [← D.map_syl]
        exact ⟨gg⁻¹ * y * gg, Subgroup.mem_subgroupOf.mpr (by simpa [hgg] using hy'), rfl⟩
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨τ, hτ, rfl⟩
      rw [← D.map_syl] at hτ
      obtain ⟨x, hx, rfl⟩ := hτ
      refine ⟨gg * x * gg⁻¹, ?_, ?_⟩
      · have hx' : (x : G) ∈ stab δ ⊓ stab μ := hx
        show ((gg * x * gg⁻¹ : ↥(stab δ)) : G) ∈ stab δ ⊓ stab ν
        rw [hAνeq, mem_conjSub]
        simpa [hgg, mul_assoc] using hx'
      · simp [MulAut.conj_apply]
  have heq : fixW D.mod S5Syl =
      fixW D.mod (((stab δ ⊓ stab ν).subgroupOf (stab δ)).map D.θ) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [himg, card_fixW_conj]
  refine D.fixSecIn_eq_of_fixW_eq hAμ hAν ?_
  rw [D.map_syl]
  exact heq

theorem c3_index_That (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') {μ : Geo H M} (hμ : μ ∈ nbrs δ) {K : Subgroup G}
    (hK : K ≤ stab δ ⊓ stab μ) (hKe : IsElemAbelian 2 K) (h4 : (K ⊓ Qv δ).relIndex K = 4)
    (hKodd : ∃ k ∈ K, k ∉ oTwoRes (stab δ) ⊔ Qv δ) :
    16 ≤ (fixSecIn K (Cb δ) (Vn δ)).relIndex (Vn δ) := by
  obtain ⟨D⟩ := nonempty_c3Data hG hirr h15 hng hp hμ
  have hKS : K ≤ stab δ := hK.trans inf_le_left
  set B := (K.subgroupOf (stab δ)).map D.θ with hB
  have hBle : B ≤ S5Syl := by
    rw [← D.map_syl]
    exact Subgroup.map_mono (fun x hx => hK hx)
  have hexp : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have hk2 := hKe.2 (k : G) hk
    have : k * k = 1 := Subtype.ext (by simpa [pow_two] using hk2)
    rw [← map_mul, this, map_one]
  have hcardB : Nat.card B = 4 := by
    set f : ↥K →* Perm (Fin 5) := D.θ.comp (Subgroup.inclusion hKS) with hf
    have hrange : f.range = B := by
      ext σ
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨⟨k, hKS k.2⟩, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩
    have hker : f.ker = (Qv δ).subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact D.ker_iff ⟨k, hKS k.2⟩
    rw [← hrange, ← Subgroup.index_ker, hker, ← Subgroup.inf_subgroupOf_left]
    exact h4
  have hBne : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcardB
    omega
  rcases le_syl_cases hBle hexp hBne with ⟨t, -, -, -, hc⟩ | hT | hT
  · omega
  · exfalso
    obtain ⟨k, hk, hkn⟩ := hKodd
    refine hkn (mem_oTwoRes_sup_of_alt D.surj D.ker_iff (hKS hk) ?_)
    have : D.θ ⟨k, hKS hk⟩ ∈ B := ⟨⟨k, hKS hk⟩, hk, rfl⟩
    rw [hT] at this
    exact (inf_le_right : S5T ≤ alternatingGroup (Fin 5)) this
  · rw [D.relIndex_fixSecIn hKS, ← hB, hT]
    have h1 := D.shape2.index_That 1
    have hid : S5That.map (MulAut.conj (1 : Perm (Fin 5))).toMonoidHom = S5That := by
      have : (MulAut.conj (1 : Perm (Fin 5))).toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun x => by simp
      rw [this, Subgroup.map_id]
    rwa [hid] at h1

end S34

end F53.Stellmacher

end CFSG.Quasithin
