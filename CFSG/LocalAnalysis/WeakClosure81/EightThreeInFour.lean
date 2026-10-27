module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeE
public import CFSG.LocalAnalysis.WeakClosure81.EightFour
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp83K (V H K : Subgroup G) : Prop where
  le_K : V ≤ K
  K_le_H : K ≤ H
  K_le_conjClosure : K ≤ conjClosure V H
  conjSubgroup_le_normalizer : ∀ x ∈ H, conjSubgroup V x ≤ Subgroup.normalizer (K : Set G)
  inf_normalizer_le : H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (K : Set G)
  conjSubgroup_le_centralizer : ∀ x ∈ H, x ∉ Subgroup.normalizer (K : Set G) →
    conjSubgroup K x ≤ Subgroup.centralizer (K : Set G)
  inf_centralizer_eq_bot : V ⊓ Subgroup.centralizer (K : Set G) = ⊥

namespace Hyp83K

variable {V H T K : Subgroup G}

theorem isSylowIn_inf_normalizer (hK : Hyp83K V H K) (h : Hyp83 V H T) :
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (K : Set G)) := by
  have hTle : T ≤ H ⊓ Subgroup.normalizer (K : Set G) :=
    fun t ht => ⟨h.T_le_H ht, hK.inf_normalizer_le (h.sylow.le ht)⟩
  refine ⟨hTle, h.sylow.isPGroup, fun hdvd => h.sylow_H.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T (H ⊓ Subgroup.normalizer (K : Set G)) H hTle
    inf_le_left]
  exact Dvd.dvd.mul_right hdvd _

theorem exists_conjSubgroup_inf_normalizer_le (hK : Hyp83K V H K) (h : Hyp83 V H T)
    {U : Subgroup G} (hUH : U ≤ H) (hU2 : IsPGroup 2 ↥U) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (K : Set G),
      conjSubgroup (U ⊓ Subgroup.normalizer (K : Set G)) n ≤ T := by
  have hsyl : IsSylowTwoOf T (H ⊓ Subgroup.normalizer (K : Set G)) :=
    hK.isSylowIn_inf_normalizer h
  obtain ⟨y, hy, hyT⟩ := exists_conj_le_of_isSylowTwoOf hsyl (inf_le_inf_right _ hUH)
    (hU2.to_le inf_le_left)
  refine ⟨y⁻¹, Subgroup.inv_mem _ hy, fun z hz => hyT ?_⟩
  rw [mem_cjSub]
  rw [mem_conjSubgroup_iff, inv_inv] at hz
  exact hz

theorem mem_normalizer_or_mul_mem (hK : Hyp83K V H K) (h : Hyp83 V H T) {U : Subgroup G}
    (hUV : ∃ g, U = conjSubgroup V g) (hUH : U ≤ H)
    (hUE : U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥) {u : G} (hu : u ∈ U)
    (hun : u ∉ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ U) :
    x ∈ Subgroup.normalizer (K : Set G) ∨ u * x ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hxn, huxn⟩ := hcon
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.inf_eSub_ne_bot
  have hzV : z ∈ V := hz.1
  have hzE : z ∈ eSub V H T := hz.2
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hu1 : u ≠ 1 := fun h1 => hun (h1 ▸ Subgroup.one_mem _)
  have hid := h.eSub_mul_conj_eq hUV hUH hUE hu hx hu1 hzE
  have hcent : ∀ y ∈ U, y ∉ Subgroup.normalizer (K : Set G) →
      conjSubgroup K y ≤ Subgroup.centralizer (K : Set G) :=
    fun y hy hyn => hK.conjSubgroup_le_centralizer y (hUH hy) hyn
  have hKz : z ∈ K := hK.le_K hzV
  have hb : u⁻¹ * z * u ∈ conjSubgroup K u := by
    rw [mem_conjSubgroup_iff, show u * (u⁻¹ * z * u) * u⁻¹ = z by group]
    exact hKz
  have hc : x⁻¹ * z * x ∈ conjSubgroup K x := by
    rw [mem_conjSubgroup_iff, show x * (x⁻¹ * z * x) * x⁻¹ = z by group]
    exact hKz
  have hd : (u * x)⁻¹ * z * (u * x) ∈ conjSubgroup K (u * x) := by
    rw [mem_conjSubgroup_iff,
      show (u * x) * ((u * x)⁻¹ * z * (u * x)) * (u * x)⁻¹ = z by group]
    exact hKz
  have hzc : z ∈ Subgroup.centralizer (K : Set G) :=
    mem_centralizer_of_mul_eq_mul (hcent u hu hun) (hcent x hx hxn)
      (hcent (u * x) (U.mul_mem hu hx) huxn) hb hc hd hid
  have hmem : z ∈ V ⊓ Subgroup.centralizer (K : Set G) := ⟨hzV, hzc⟩
  rw [hK.inf_centralizer_eq_bot] at hmem
  exact hz1' (Subgroup.mem_bot.mp hmem)

theorem le_normalizer_of_inf_centralizer_ne_bot (hK : Hyp83K V H K) (h : Hyp83 V H T)
    {U : Subgroup G} (hUV : ∃ g, U = conjSubgroup V g) (hUH : U ≤ H)
    (hUE : U ⊓ Subgroup.centralizer (eSub V H T : Set G) ≠ ⊥) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  rcases eight_two h.elemAbelian h.isTI h.ne_bot h.isCalH h.sylow hUV hUH hUE with
    hcomm | ⟨-, x, hx, rfl⟩
  · have hKU : K ≤ Subgroup.centralizer (U : Set G) :=
      hK.K_le_conjClosure.trans (conjClosure_le fun y hy z hz => by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hzy : y * z * y⁻¹ ∈ conjSubgroup V y⁻¹ := by
          rw [mem_conjSubgroup_iff, show y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ = z by group]
          exact hz
        exact hcomm y⁻¹ (H.inv_mem hy) u hu (y * z * y⁻¹) hzy)
    exact (Subgroup.le_centralizer_iff.mp hKU).trans (Subgroup.centralizer_le_normalizer _)
  · exact hK.conjSubgroup_le_normalizer x hx

theorem le_normalizer_of_inf_normalizer_le (hK : Hyp83K V H K) (h : Hyp83 V H T)
    {U : Subgroup G} (hUV : ∃ g, U = conjSubgroup V g) (hUH : U ≤ H)
    (hUT : U ⊓ Subgroup.normalizer (K : Set G) ≤ T) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  by_cases hUE : U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥
  · by_contra hUN
    obtain ⟨u, hu, hun⟩ := Set.not_subset.mp hUN
    have hcard : 2 < Nat.card U := by
      obtain ⟨g, rfl⟩ := hUV
      rw [card_conjSubgroup']
      exact h.two_lt_card
    have hne : U ⊓ Subgroup.normalizer (K : Set G) ≠ ⊥ :=
      inf_ne_bot_of_forall_mem_or_mul_mem hcard hu fun x hx =>
        hK.mem_normalizer_or_mul_mem h hUV hUH hUE hu hun hx
    have hN : U ⊓ Subgroup.normalizer (V : Set G) ≠ ⊥ :=
      ne_bot_of_le_ne_bot hne (le_inf inf_le_left (hUT.trans h.T_le_normalizer))
    apply hun
    rcases two_conj_eq_or_comm h.elemAbelian h.isTI hUV
      ⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩ hN with hcomm | ⟨y, hy, hVy⟩
    · have hUV' : U ≤ Subgroup.centralizer (V : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hcomm w hw v hv).symm
      exact (le_inf hUH (hUV'.trans (Subgroup.centralizer_le_normalizer _))).trans
        hK.inf_normalizer_le hu
    · have hyH : y ∈ H := sup_le hUH h.le_H hy
      have hUy : U = conjSubgroup V y⁻¹ := by
        rw [hVy, CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
          CFSG.Quasithin.conjSubgroup_one]
      have hle := hK.conjSubgroup_le_normalizer y⁻¹ (H.inv_mem hyH)
      rw [hUy] at hu
      exact hle hu
  · exact hK.le_normalizer_of_inf_centralizer_ne_bot h hUV hUH hUE

theorem le_normalizer_of_conj_le_H (hK : Hyp83K V H K) (h : Hyp83 V H T) {U : Subgroup G}
    (hUV : ∃ g, U = conjSubgroup V g) (hUH : U ≤ H) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨g, rfl⟩ := hUV
  have hU2 : IsPGroup 2 ↥(conjSubgroup V g) :=
    (isElemAbelian_conjSubgroup' h.elemAbelian g).isPGroup
  obtain ⟨n, hn, hnT⟩ := hK.exists_conjSubgroup_inf_normalizer_le h hUH hU2
  have hNn : conjSubgroup (Subgroup.normalizer (K : Set G)) n =
      Subgroup.normalizer (K : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hn.2)
  have hHn : conjSubgroup H n = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hn.1)
  have hinf : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (K : Set G)) n =
      conjSubgroup (conjSubgroup V g) n ⊓
        conjSubgroup (Subgroup.normalizer (K : Set G)) n :=
    Subgroup.map_inf _ _ (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective
  have hcore := hK.le_normalizer_of_inf_normalizer_le h
    (U := conjSubgroup (conjSubgroup V g) n)
    ⟨g * n, CFSG.Quasithin.conjSubgroup_conjSubgroup V g n⟩
    (by rw [← hHn]; exact Subgroup.map_mono hUH)
    (by rw [← hNn, ← hinf]; exact hnT)
  intro y hy
  have hy' : n⁻¹ * y * n ∈ conjSubgroup (conjSubgroup V g) n := by
    rw [mem_conjSubgroup_iff, show n * (n⁻¹ * y * n) * n⁻¹ = y by group]
    exact hy
  have hn' : n ∈ Subgroup.normalizer (K : Set G) := hn.2
  have hmem := Subgroup.mul_mem _ (Subgroup.mul_mem _ hn' (hcore hy')) (Subgroup.inv_mem _ hn')
  rwa [show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at hmem

theorem wClos_le_normalizer_conjSubgroup (hK : Hyp83K V H K) (h : Hyp83 V H T) {x : G}
    (hx : x ∈ H) :
    E3.wClos V 0 T ≤ Subgroup.normalizer (conjSubgroup K x : Set G) := by
  rw [wClos_zero_eq_iSup h.elemAbelian]
  refine iSup₂_le fun g hg => ?_
  have hUH : conjSubgroup (conjSubgroup V g) x⁻¹ ≤ H := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hyH : x⁻¹ * y * (x⁻¹)⁻¹ ∈ H := h.T_le_H (hg hy)
    have hmem := H.mul_mem (H.mul_mem hx hyH) (H.inv_mem hx)
    rwa [show x * (x⁻¹ * y * (x⁻¹)⁻¹) * x⁻¹ = y by group] at hmem
  have hN := hK.le_normalizer_of_conj_le_H h
    ⟨g * x⁻¹, CFSG.Quasithin.conjSubgroup_conjSubgroup V g x⁻¹⟩ hUH
  rw [← conjSubgroup_normalizer]
  intro y hy
  rw [mem_conjSubgroup_iff]
  refine hN ?_
  rw [mem_conjSubgroup_iff, show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group]
  exact hy

theorem exists_mem_inf_normalizer_wClos_conjSubgroup_eq (hK : Hyp83K V H K) (h : Hyp83 V H T)
    {x : G} (hx : x ∈ H) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G),
      conjSubgroup K n = conjSubgroup K x := by
  have hW1 : E3.wClos V 0 T ≤ Subgroup.normalizer (K : Set G) := by
    simpa [conjSubgroup_one] using hK.wClos_le_normalizer_conjSubgroup h H.one_mem
  exact exists_conjSubgroup_eq_of_weaklyClosedIn (V := K) (W := E3.wClos V 0 T)
    (T := T) (H := H) (wClos_zero_le V T) ((wClos_zero_le V T).trans h.T_le_H) h.T_le_H
    (fun y _ hy => wClos_zero_isWeaklyClosedIn h.elemAbelian y hy) h.sylow_H
    hK.K_le_H hW1 hx (hK.wClos_le_normalizer_conjSubgroup h hx)

theorem coe_eq_mul_mul (hK : Hyp83K V H K) (h : Hyp83 V H T)
    (h3 : ((H ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) =
      (K : Set G) * ((H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G)) :
    (H : Set G) = (K : Set G) * ((H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) *
      ((H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, hnx⟩ := hK.exists_mem_inf_normalizer_wClos_conjSubgroup_eq h hx
    have hm : x * n⁻¹ ∈ H ⊓ Subgroup.normalizer (K : Set G) :=
      ⟨H.mul_mem hx (H.inv_mem hn.1),
        conjSubgroup_eq_conjSubgroup_iff_mul_inv_mem.mp hnx.symm⟩
    have hm' := hm
    rw [← SetLike.mem_coe, h3] at hm'
    obtain ⟨k, hk, v, hv, hkv⟩ := hm'
    have hkv' : k * v = x * n⁻¹ := hkv
    exact ⟨k * v, ⟨k, hk, v, hv, rfl⟩, n, hn, by show k * v * n = x; rw [hkv']; group⟩
  · rintro ⟨y, ⟨k, hk, v, hv, rfl⟩, n, hn, rfl⟩
    exact H.mul_mem (H.mul_mem (hK.K_le_H hk) hv.1) hn.1

end Hyp83K

end CFSG.LocalAnalysis.WeakClosure81

end
