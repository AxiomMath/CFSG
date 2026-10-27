module

public import CFSG.Quasithin.EmptyFaithful.SzF53MNat
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.F53Mod

open Equiv CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem SecData.twist {n : ℕ} {M : Model n} {K L X : Subgroup G} [(L.subgroupOf X).Normal]
    {Ψ : ↥K →* Perm (Fin n)} {β : M.W →* ↥X ⧸ L.subgroupOf X} (h : SecData M K L X Ψ β)
    (g : Perm (Fin n)) :
    SecData M K L X ((MulAut.conj g).toMonoidHom.comp Ψ) (β.comp (M.act g⁻¹).toMonoidHom) where
  surj := by
    intro q
    obtain ⟨u, rfl⟩ := h.surj q
    exact ⟨M.act g u, by show β (M.act g⁻¹ (M.act g u)) = β u; rw [act_inv_act]⟩
  inj := by
    intro u v huv
    have := h.inj huv
    exact (M.act g⁻¹).injective this
  equiv := by
    intro k u x hu
    obtain ⟨hkx, h1⟩ := h.equiv k (M.act g⁻¹ u) x hu
    refine ⟨hkx, ?_⟩
    show β (M.act g⁻¹ (M.act (g * Ψ k * g⁻¹) u)) = _
    rw [← h1]
    congr 1
    rw [← act_mul_apply, ← act_mul_apply]
    congr 1
    group

theorem sign_conj_five (g σ : Perm (Fin 5)) :
    Perm.sign (g * σ * g⁻¹) = Perm.sign σ := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm (Perm.sign g) (Perm.sign σ),
    mul_assoc, Int.units_mul_self, mul_one]

theorem card_image_sylow {F S₀ : Subgroup G} {θ : ↥F →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hS : IsSylowTwoOf S₀ F) :
    Nat.card ((S₀.subgroupOf F).map θ) = 8 := by
  obtain ⟨-, hp, hodd⟩ := hS
  have hp' : IsPGroup 2 ↥(S₀.subgroupOf F) := by
    intro x
    obtain ⟨k, hk⟩ := hp ⟨(x.1 : G), x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥S₀ => (y : G)) hk
    simpa using this
  have hPp : IsPGroup 2 ↥((S₀.subgroupOf F).map θ) := hp'.map θ
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  have hidx : ¬ 2 ∣ ((S₀.subgroupOf F).map θ).index := fun hd =>
    hodd (hd.trans (Subgroup.index_map_dvd _ hθs))
  have hmul := Subgroup.card_mul_index ((S₀.subgroupOf F).map θ)
  rw [hk, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hmul
  have h120 : (Nat.factorial 5) = 120 := rfl
  rw [h120] at hmul
  have hk6 : k ≤ 6 := by
    by_contra hcon
    have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < ((S₀.subgroupOf F).map θ).index := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0] at hidx; exact hidx (dvd_zero 2))
    have : 2 ^ k * ((S₀.subgroupOf F).map θ).index ≥ 2 ^ 7 := by nlinarith
    omega
  have hodd' : ((S₀.subgroupOf F).map θ).index % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one ((S₀.subgroupOf F).map θ).index with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hidx
    · exact h
  rw [hk]
  interval_cases k <;> omega

theorem mem_oTwoRes_sup_iff {F L X : Subgroup G} [Finite G] {θ : ↥F →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hk : θ.ker = (cSecIn F L X).subgroupOf F) {f : G} (hf : f ∈ F) :
    f ∈ oTwoRes F ⊔ cSecIn F L X ↔ θ ⟨f, hf⟩ ∈ alternatingGroup (Fin 5) := by
  have hC : cSecIn F L X ≤ F := (Subgroup.closure_le F).mpr fun _ hx => hx.1
  constructor
  · intro hmem
    have hle : oTwoRes F ⊔ cSecIn F L X ≤
        ((alternatingGroup (Fin 5)).comap θ).map F.subtype := by
      refine sup_le ?_ ?_
      · refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨hxF, m, hm, hxm⟩
        refine ⟨⟨x, hxF⟩, ?_, rfl⟩
        show θ ⟨x, hxF⟩ ∈ alternatingGroup (Fin 5)
        rw [Equiv.Perm.mem_alternatingGroup]
        have h1 : Perm.sign (θ ⟨x, hxF⟩) ^ m = 1 := by
          rw [← map_pow, ← map_pow]
          have : (⟨x, hxF⟩ : ↥F) ^ m = 1 := Subtype.ext (by simpa using hxm)
          rw [this]; simp
        rcases Int.units_eq_one_or (Perm.sign (θ ⟨x, hxF⟩)) with h | h
        · exact h
        · rw [h, hm.neg_one_pow] at h1
          exact absurd h1 (by decide)
      · intro x hx
        refine ⟨⟨x, hC hx⟩, ?_, rfl⟩
        show θ ⟨x, hC hx⟩ ∈ alternatingGroup (Fin 5)
        rw [Equiv.Perm.mem_alternatingGroup]
        have : θ ⟨x, hC hx⟩ = 1 := (mem_cSecIn_iff_of_ker hk (hC hx)).mpr hx
        rw [this]; simp
    obtain ⟨y, hy, hyf⟩ := hle hmem
    have : y = ⟨f, hf⟩ := Subtype.ext hyf
    rw [← this]
    exact Subgroup.mem_comap.mp hy
  · intro hA
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
    have hA5 : alternatingGroup (Fin 5) ≤ ((oTwoRes F).subgroupOf F).map θ := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro τ hτ
      obtain ⟨o, hoF, hodd, ho, hθo⟩ := hthree τ hτ
      exact ⟨⟨o, hoF⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨hoF, hodd⟩), hθo⟩
    obtain ⟨o, hoO, hoθ⟩ := hA5 hA
    have hoF : (o : G) ∈ oTwoRes F := Subgroup.mem_subgroupOf.mp hoO
    have hcf : f * (o : G)⁻¹ ∈ cSecIn F L X := by
      have h1 : θ (⟨f, hf⟩ * o⁻¹) = 1 := by rw [map_mul, map_inv, hoθ]; simp
      have := (mem_cSecIn_iff_of_ker hk (F.mul_mem hf (F.inv_mem o.2))).mp h1
      simpa using this
    have : f = (f * (o : G)⁻¹) * (o : G) := by group
    rw [sup_comm, this]
    exact Subgroup.mul_mem_sup hcf hoF

theorem SecData.act_trivial_iff {n : ℕ} {M : Model n} {K L X : Subgroup G}
    [(L.subgroupOf X).Normal] {Ψ : ↥K →* Perm (Fin n)} {β : M.W →* ↥X ⧸ L.subgroupOf X}
    (h : SecData M K L X Ψ β) {U : Subgroup G} (hUX : U ≤ X) {Y : Subgroup M.W}
    (hYm : Y.map β = (U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X))) {s : G}
    (hs : s ∈ K) :
    (∀ x ∈ U, s * x * s⁻¹ * x⁻¹ ∈ L) ↔ ∀ y ∈ Y, M.act (Ψ ⟨s, hs⟩) y = y := by
  constructor
  · intro hx y hy
    have hy' : β y ∈ (U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) :=
      hYm ▸ ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hcy⟩ := hy'
    obtain ⟨hsc, h1⟩ := h.equiv ⟨s, hs⟩ y c hcy.symm
    apply h.inj
    rw [h1, ← hcy]
    refine mk_eq_iff_mem.mpr ?_
    have e : (c : G) * (s * (c : G) * s⁻¹)⁻¹ = (s * (c : G) * s⁻¹ * (c : G)⁻¹)⁻¹ := by group
    show (c : G) * (s * (c : G) * s⁻¹)⁻¹ ∈ L
    rw [e]
    exact L.inv_mem (hx _ (Subgroup.mem_subgroupOf.mp hc))
  · intro hy x hx
    have hx' : (QuotientGroup.mk' (L.subgroupOf X)) ⟨x, hUX hx⟩ ∈ Y.map β := by
      rw [hYm]; exact ⟨⟨x, hUX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨y, hyY, hβy⟩ := hx'
    obtain ⟨hsx, h1⟩ := h.equiv ⟨s, hs⟩ y ⟨x, hUX hx⟩ hβy
    rw [hy y hyY, hβy] at h1
    have := mk_eq_iff_mem.mp h1
    simpa using this

theorem map_conj_map_conj_inv (B : Subgroup (Perm (Fin 5))) (g : Perm (Fin 5)) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  ext τ
  rw [mem_map_conj, mem_map_conj, show g⁻¹ * (g⁻¹⁻¹ * τ * g⁻¹) * g = τ by group]

theorem card_S5T : Nat.card S5T = 4 := by
  have h : S5TF.card = 4 := by decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5T_iff)

theorem SecData.exists_normalized {M : Model 5} {F L X S₀ : Subgroup G}
    [(L.subgroupOf X).Normal] {θ : ↥F →* Perm (Fin 5)} {β : M.W →* ↥X ⧸ L.subgroupOf X}
    (hθs : Function.Surjective θ) (hθk : θ.ker = (cSecIn F L X).subgroupOf F)
    (hsd : SecData M F L X θ β) (hS : IsSylowTwoOf S₀ F) :
    ∃ (Ψ : ↥F →* Perm (Fin 5)) (β' : M.W →* ↥X ⧸ L.subgroupOf X), Function.Surjective Ψ ∧
      Ψ.ker = (cSecIn F L X).subgroupOf F ∧ SecData M F L X Ψ β' ∧
      (S₀.subgroupOf F).map Ψ = S5Syl ∧ ∀ f, Perm.sign (Ψ f) = Perm.sign (θ f) := by
  obtain ⟨g₀, hg₀⟩ := exists_conj_S5Syl (card_image_sylow hθs hS)
  refine ⟨(MulAut.conj g₀⁻¹).toMonoidHom.comp θ, β.comp (M.act (g₀⁻¹)⁻¹).toMonoidHom,
    (MulEquiv.surjective (MulAut.conj g₀⁻¹)).comp hθs, ?_, hsd.twist g₀⁻¹, ?_,
    fun f => sign_conj_five _ _⟩
  · rw [← hθk]
    ext f
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (MulAut.conj g₀⁻¹).map_eq_one_iff
  · rw [← Subgroup.map_map, hg₀, map_conj_map_conj_inv]

theorem IsNatSec.centralizer_l2 {F L X : Subgroup G} [Finite G] (h : IsNatSec F L X)
    {S₀ : Subgroup G} (hS : IsSylowTwoOf S₀ F) {U : Subgroup G} (hLU : L ≤ U) (hUX : U ≤ X)
    (hn : S₀ ≤ Subgroup.normalizer (U : Set G)) (h4 : L.relIndex U = 4) :
    cSecIn S₀ L U = S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X) ∧
      (cSecIn F L X).relIndex (S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X)) = 4 := by
  have hLX : L ≤ X := hLU.trans hUX
  have hsec := IsModelSec.isSec h hLX
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := h
  have hS₀F : S₀ ≤ F := hS.1
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hinvU : ∀ k ∈ S₀, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    ((Subgroup.mem_normalizer_iff.mp (hn hk)) u).mp hu
  obtain ⟨Y, hY, hYm⟩ := (hsd'.invariant_iff_sub hS₀F hLU hUX).mp hinvU
  have hYinv : IsInvSub nat S5Syl Y := by rw [← hPS]; exact hY
  have hYcard : Nat.card Y = 4 := by
    have h1 : Nat.card (Y.map β') = Nat.card Y := Subgroup.card_map_of_injective hsd'.inj
    rw [← h1, hYm]
    have hk : (QuotientGroup.mk' (L.subgroupOf X)).ker = L.subgroupOf X :=
      QuotientGroup.ker_mk' _
    rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hUX, h4]
  have hmemΨ : ∀ s : G, ∀ hs : s ∈ S₀, Ψ ⟨s, hS₀F hs⟩ ∈ S5Syl := fun s hs => by
    rw [← hPS]; exact ⟨⟨s, hS₀F hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hcS : ∀ s : G, ∀ hs : s ∈ S₀, s ∈ cSecIn S₀ L U ↔ s ∈ oTwoRes F ⊔ cSecIn F L X := by
    intro s hs
    have h1 : s ∈ cSecIn S₀ L U ↔ ∀ x ∈ U, s * x * s⁻¹ * x⁻¹ ∈ L := by
      constructor
      · intro hmem
        exact (X1512.mem_cSecIn_of_normalizes (hS₀F.trans hsec.normL) hmem).2
      · intro hall
        exact Subgroup.subset_closure ⟨hs, hall⟩
    rw [h1, hsd'.act_trivial_iff hUX hYm (hS₀F hs),
      nat_centralizer_l2 (hmemΨ s hs) Y hYinv hYcard, mem_oTwoRes_sup_iff hθs hθk (hS₀F hs)]
    simp only [Equiv.Perm.mem_alternatingGroup, hsgn]
  constructor
  · ext s
    constructor
    · intro hs
      have hsS : s ∈ S₀ := ((Subgroup.closure_le S₀).mpr fun _ hx => hx.1) hs
      exact ⟨hsS, (hcS s hsS).mp hs⟩
    · rintro ⟨hsS, hs⟩
      exact (hcS s hsS).mpr hs
  · have hCF : cSecIn F L X ≤ F := (Subgroup.closure_le F).mpr fun _ hx => hx.1
    have hDF : S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X) ≤ F := inf_le_left.trans hS₀F
    rw [← Subgroup.relIndex_subgroupOf hDF, ← hkΨ, Subgroup.relIndex_ker]
    have hmap : ((S₀ ⊓ (oTwoRes F ⊔ cSecIn F L X)).subgroupOf F).map Ψ = S5T := by
      ext τ
      constructor
      · rintro ⟨d, hd, rfl⟩
        have hd' := Subgroup.mem_subgroupOf.mp hd
        refine Subgroup.mem_inf.mpr ⟨hmemΨ d hd'.1, ?_⟩
        have := (mem_oTwoRes_sup_iff hθs hθk d.2).mp hd'.2
        rw [Equiv.Perm.mem_alternatingGroup] at this ⊢
        rw [hsgn]; exact this
      · intro hτ
        obtain ⟨hτS, hτA⟩ := Subgroup.mem_inf.mp hτ
        rw [← hPS] at hτS
        obtain ⟨d, hd, rfl⟩ := hτS
        have hdS : (d : G) ∈ S₀ := Subgroup.mem_subgroupOf.mp hd
        refine ⟨d, Subgroup.mem_subgroupOf.mpr ⟨hdS, ?_⟩, rfl⟩
        refine (mem_oTwoRes_sup_iff hθs hθk d.2).mpr ?_
        rw [Equiv.Perm.mem_alternatingGroup] at hτA ⊢
        rwa [hsgn] at hτA
    rw [hmap, card_S5T]

end CFSG.Quasithin.F53Mod
