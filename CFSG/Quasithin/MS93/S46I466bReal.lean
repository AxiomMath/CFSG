module

public import CFSG.Quasithin.MS93.S46I466bLin
public import CFSG.Quasithin.MS93.S46I464Loc

public section

namespace CFSG.Quasithin.MS93.S46.I466b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464
open scoped Matrix commutatorElement

section Grp

variable {𝔾 : Type*} [Group 𝔾]

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup 𝔾}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {g : 𝔾} (hg : g ∈ H ⊔ K) :
    ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  have hHN : H ≤ Subgroup.normalizer (K : Set 𝔾) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hc x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hy' : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [hy']
      have e := hc x⁻¹ (H.inv_mem hx) _ hy
      rw [e, inv_mul_cancel_right]
      exact hy
  have hg' : g ∈ ((H ⊔ K : Subgroup 𝔾) : Set 𝔾) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H K hHN] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem card_sup_mul_card_inf_of_commute {H K : Subgroup 𝔾} [Finite H] [Finite K]
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  let f : H × K →* 𝔾 := H.subtype.noncommCoprod K.subtype (fun x y => hc x x.2 y y.2)
  have hf : ∀ (x : H) (y : K), f (x, y) = (x : 𝔾) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hrange : f.range = H ⊔ K := by
    ext g
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      rw [hf]
      exact Subgroup.mul_mem_sup x.2 y.2
    · intro hg
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hf _ _⟩
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ K) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : 𝔾), k.1.1.2, by
          have h1 : (k.1.1 : 𝔾) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hf] at this
          rw [eq_inv_of_mul_eq_one_left h1]
          exact K.inv_mem k.1.2.2⟩
        invFun := fun g => ⟨(⟨g, g.2.1⟩, ⟨(g : 𝔾)⁻¹, K.inv_mem g.2.2⟩), by
          rw [MonoidHom.mem_ker, hf]
          exact mul_inv_cancel _⟩
        left_inv := fun k => by
          refine Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext ?_))
          have h1 : (k.1.1 : 𝔾) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hf] at this
          exact inv_eq_of_mul_eq_one_right h1
        right_inv := fun g => Subtype.ext rfl }
  have h := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm]
  exact h

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
include h hφ

omit [Fintype F] hφ in
theorem exists_uloc_mul_zloc (hfull : IsSL3Full M T L) {y : Vtx (puAmalgam h.le)}
    (hy : IsMVtx _ y) {z : (puAmalgam h.le).Universal} (hz : z ∈ ZM (puAmalgam h.le) y) :
    ∃ u ∈ Uloc h.le L y, ∃ ζ ∈ Zloc h.le L y, z = u * ζ := by
  rw [zm_eq_uloc_sup_zloc h hfull hy] at hz
  refine exists_mul_of_mem_sup_of_commute (fun u hu ζ hζ => ?_) hz
  exact (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hy hζ) u
    (puTrans_le_stab h.le _ y hu))

include h464 hsq in
theorem fixN_natImage_qv {y ρ : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hyρ : (puAmalgam h.le).treeGraph.Adj y ρ)
    {ψ : ↥(stab (puAmalgam h.le) y) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ y) (Uloc h.le L y) ⊥ ψ false 1) :
    Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 ∧
      commN (natImage ψ (Qv (puAmalgam h.le) ρ)) = fixN (natImage ψ (Qv _ ρ)) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ y := qv_le_stab_of_adj _ hyρ.symm
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc := card_uloc_inf_centralizer_qv h hφ h464 hy hyρ (hsq y ρ hy hyρ)
  rw [card_inf_centralizer_eq_pow hψ hT, ← Nat.card_eq_fintype_card] at hc
  have h2 : Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 :=
    Nat.pow_right_injective hq hc
  have hle : commN (natImage ψ (Qv (puAmalgam h.le) ρ)) ≤ fixN (natImage ψ (Qv _ ρ)) := by
    refine commN_le_fixN_of_commutator_le_centralizer hψ hT ?_
    rw [← S4A.usup_eq_commutator_uloc h hfull hy hyρ]
    exact (h464 y ρ hy hyρ).trans (zh_le_centralizer _ ρ)
  have hcard := card_commutator_eq_pow hψ hT
  rw [← S4A.usup_eq_commutator_uloc h hfull hy hyρ, hsq y ρ hy hyρ,
    ← Nat.card_eq_fintype_card] at hcard
  have hc2 : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 :=
    (Nat.pow_right_injective hq hcard).symm
  exact ⟨h2, Submodule.eq_of_le_of_finrank_eq hle (by rw [hc2, h2])⟩

include h464 hsq h466 in
theorem natImage_qv_eq_axisGroup {y ρ : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hyρ : (puAmalgam h.le).treeGraph.Adj y ρ)
    {ψ : ↥(stab (puAmalgam h.le) y) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ y) (Uloc h.le L y) ⊥ ψ false 1) :
    natImage ψ (Qv (puAmalgam h.le) ρ) = axisGroup (fixN (natImage ψ (Qv _ ρ))) := by
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ y := qv_le_stab_of_adj _ hyρ.symm
  obtain ⟨h2, hcf⟩ := fixN_natImage_qv h hφ h464 hsq hy hyρ hψ
  have hle : natImage ψ (Qv (puAmalgam h.le) ρ) ≤ axisGroup (fixN (natImage ψ (Qv _ ρ))) :=
    fun B hB => ⟨fun p hp => hp B hB, fun x => hcf ▸ sub_mem_commN hB x⟩
  have : Finite ↥(axisGroup (fixN (natImage ψ (Qv (puAmalgam h.le) ρ)))) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_natImage_eq_relIndex h hφ hy hψ hT, h466 y ρ hy hyρ, ← Nat.card_eq_fintype_card]
  exact card_axisGroup_le h2

include h464 hsq h466 in
theorem mem_normalizer_qv_of_toSL3 {y ρ : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hyρ : (puAmalgam h.le).treeGraph.Adj y ρ)
    {ψ : ↥(stab (puAmalgam h.le) y) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ y) (Uloc h.le L y) ⊥ ψ false 1)
    {g : ↥(stab (puAmalgam h.le) y)}
    (hg : ∀ p ∈ fixN (natImage ψ (Qv (puAmalgam h.le) ρ)),
      ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ fixN (natImage ψ (Qv _ ρ))) :
    (g : (puAmalgam h.le).Universal) ∈ Subgroup.normalizer (Qv (puAmalgam h.le) ρ : Set _) := by
  have h20 := h.hyp20
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ y := qv_le_stab_of_adj _ hyρ.symm
  have hQT : Qv (puAmalgam h.le) y ≤ Qv _ ρ := qv_le_qv _ h20 hy hyρ
  have heq := natImage_qv_eq_axisGroup h hφ h464 hsq h466 hy hyρ hψ
  obtain ⟨h2, -⟩ := fixN_natImage_qv h hφ h464 hsq hy hyρ hψ
  have : FiniteDimensional F ↥(fixN (natImage ψ (Qv (puAmalgam h.le) ρ))) := inferInstance
  have key : ∀ k : ↥(stab (puAmalgam h.le) y),
      (∀ p ∈ fixN (natImage ψ (Qv (puAmalgam h.le) ρ)),
        ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈
          fixN (natImage ψ (Qv _ ρ))) →
      ∀ t ∈ Qv (puAmalgam h.le) ρ, (k : (puAmalgam h.le).Universal) * t * (k : _)⁻¹ ∈
        Qv (puAmalgam h.le) ρ := by
    intro k hk t ht
    have hts : t ∈ stab (puAmalgam h.le) y := hT ht
    have hmem : toSL3 ψ (k * ⟨t, hts⟩ * k⁻¹) ∈ natImage ψ (Qv (puAmalgam h.le) ρ) := by
      rw [heq, map_mul, map_mul, map_inv]
      refine conj_mem_axisGroup hk ?_
      rw [← heq]
      exact mem_natImage.mpr ⟨⟨t, hts⟩, ht, rfl⟩
    obtain ⟨t', ht', he⟩ := mem_natImage.mp hmem
    have h1 : toSL3 ψ ((k * ⟨t, hts⟩ * k⁻¹) * t'⁻¹) = 1 := by
      rw [map_mul, map_inv, ← he, mul_inv_cancel]
    have h2 := (toSL3_eq_one_iff_mem_qv h hφ hy hψ _).mp h1
    have e : (k : (puAmalgam h.le).Universal) * t * (k : _)⁻¹ =
        ((((k * ⟨t, hts⟩ * k⁻¹) * t'⁻¹ : ↥(stab (puAmalgam h.le) y)) :
          (puAmalgam h.le).Universal)) * (t' : _) := by
      simp [mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (hQT h2) ht'
  refine mem_normalizer_of_map_conj_le ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact key g hg t ht
  · rintro _ ⟨t, ht, rfl⟩
    have := key g⁻¹ (fun p hp => by
      rw [map_inv]
      exact inv_mulVec_mem_of_le hg hp) t ht
    simpa using this

omit [Fintype F] hφ in
theorem finite_of_le_stab {y : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    {K : Subgroup (puAmalgam h.le).Universal} (hK : K ≤ stab _ y) : Finite K :=
  have := finite_stab h hy
  Finite.of_injective _ (Subgroup.inclusion_injective hK)

omit [Fintype F] hφ in
theorem uloc_comm (hfull : IsSL3Full M T L) {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    ∀ a ∈ Uloc h.le L x, ∀ b ∈ Uloc h.le L x, a * b = b * a := by
  intro a ha b hb
  have hab := (isElemAbelian_zm _ h.hyp20 h.critDist_pos hx).1
  have := hab.is_comm.comm ⟨a, uloc_le_zm h hfull hx ha⟩ ⟨b, uloc_le_zm h hfull hx hb⟩
  simpa using congrArg Subtype.val this

include h464 hsq h466 in
theorem exists_rot {x ρ : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x)
    (hxρ : (puAmalgam h.le).treeGraph.Adj x ρ) {A' : Subgroup (puAmalgam h.le).Universal}
    (hA' : A' ≤ stab _ x) (hcard : Nat.card ↥⁅Uloc h.le L x, A'⁆ = Fintype.card F)
    (hle : ⁅Uloc h.le L x, A'⁆ ≤ ⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆) :
    ∃ g : (puAmalgam h.le).Universal, g ∈ stab _ x ∧
      g ∈ Subgroup.normalizer (Qv (puAmalgam h.le) ρ : Set _) ∧ g ^ 3 = 1 ∧
      (∀ z ∈ ZM (puAmalgam h.le) x, g * z * g⁻¹ * z⁻¹ ∈ ZH _ ρ) ∧
      ⁅Uloc h.le L x, A'⁆ ⊔ (⁅Uloc h.le L x, A'⁆).map (MulAut.conj g).toMonoidHom =
        ⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ ∧
      ⁅Uloc h.le L x, A'⁆ ⊓ (⁅Uloc h.le L x, A'⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hx
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ x := qv_le_stab_of_adj _ hxρ.symm
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨h2, hcf⟩ := fixN_natImage_qv h hφ h464 hsq hx hxρ hψ
  set P := fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) with hPdef
  set R' := ⁅Uloc h.le L x, A'⁆ with hR'def
  have hUs : Uloc h.le L x ≤ stab _ x := puTrans_le_stab h.le _ x
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) x
  have hHU : ⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ = ⁅Uloc h.le L x, Qv _ ρ⁆ :=
    commutator_zm_eq_uloc h hfull hx hT
  have hmemH : ∀ u : ↥(Uloc h.le L x),
      (u : (puAmalgam h.le).Universal) ∈ ⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ ↔ natVec hψ u ∈ P := by
    intro u
    rw [hHU, mem_commutator_iff_natVec hψ hT u, hcf]
  have hmemR : ∀ u : ↥(Uloc h.le L x),
      (u : (puAmalgam h.le).Universal) ∈ R' ↔ natVec hψ u ∈ commN (natImage ψ A') :=
    fun u => mem_commutator_iff_natVec hψ hA' u
  have hℓ1 : Module.finrank F (commN (natImage ψ A')) = 1 := by
    have h1 := card_commutator_eq_pow hψ hA'
    rw [← hR'def, hcard, ← Nat.card_eq_fintype_card] at h1
    exact Nat.pow_right_injective hq
      (show Nat.card F ^ _ = Nat.card F ^ 1 by rw [pow_one]; exact h1.symm)
  obtain ⟨r, hrℓ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := commN (natImage ψ A'))
    (fun hbot => by rw [hbot, finrank_bot] at hℓ1; omega)
  have hℓP : ∀ v ∈ commN (natImage ψ A'), v ∈ P := by
    intro v hv
    obtain ⟨u, rfl⟩ := natVec_surjective hψ v
    exact (hmemH u).mp (hle ((hmemR u).mpr hv))
  have hℓeq : commN (natImage ψ A') = F ∙ r :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hrℓ)
      (by rw [finrank_span_singleton hr0, hℓ1])).symm
  obtain ⟨B, hB3, hBP, hBr⟩ := exists_rot_of_plane h2 (hℓP r hrℓ) hr0
  have hBstab : ∀ p ∈ P, ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p ∈ P := fun p hp => by
    have := P.add_mem (hBP p) hp
    rwa [sub_add_cancel] at this
  have hBn : ∀ n : ℕ, ∀ v, ((B ^ n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ P := by
    intro n
    induction n with
    | zero => intro v; rw [pow_zero, coe_one_SL3, Matrix.one_mulVec, sub_self]; exact P.zero_mem
    | succ n ih =>
      intro v
      rw [pow_succ', coe_mul_SL3, ← Matrix.mulVec_mulVec]
      have e1 : ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((B ^ n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) - v =
          (((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((B ^ n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) -
            ((B ^ n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) +
          (((B ^ n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) := by abel
      rw [e1]
      exact P.add_mem (hBP _) (ih v)
  obtain ⟨g₀, hg₀⟩ := toSL3_surjective hψs B
  have hg₀N := mem_normalizer_qv_of_toSL3 h hφ h464 hsq h466 hx hxρ hψ (g := g₀)
    (by rw [hg₀]; exact hBstab)
  have h3 : toSL3 ψ (g₀ ^ 3) = 1 := by rw [map_pow, hg₀, hB3]
  obtain ⟨e, he⟩ := pow_two_pow_eq_one_of_toSL3_eq_one h hφ hx hψ _ h3
  set g₁ : ↥(stab (puAmalgam h.le) x) := g₀ ^ 2 ^ e with hg₁
  have hg₁3 : g₁ ^ 3 = 1 := by rw [hg₁, ← pow_mul, mul_comm, pow_mul, he]
  have hψg₁ : toSL3 ψ g₁ = B ^ 2 ^ e := by rw [hg₁, map_pow, hg₀]
  have hndvd : ¬ 3 ∣ 2 ^ e := fun hd => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hg₁N : (g₁ : (puAmalgam h.le).Universal) ∈
      Subgroup.normalizer (Qv (puAmalgam h.le) ρ : Set _) := by
    rw [hg₁, Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hg₀N _
  have hg₁H : (g₁ : (puAmalgam h.le).Universal) ∈
      Subgroup.normalizer ((⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ : Subgroup _) : Set _) :=
    le_normalizer_of_map_conj_le (Z := Subgroup.zpowers (g₁ : (puAmalgam h.le).Universal))
      (fun k hk => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        have hks : (g₁ : (puAmalgam h.le).Universal) ^ n ∈ stab (puAmalgam h.le) x :=
          Subgroup.zpow_mem _ g₁.2 n
        have hkN : (g₁ : (puAmalgam h.le).Universal) ^ n ∈
            Subgroup.normalizer (Qv (puAmalgam h.le) ρ : Set _) := Subgroup.zpow_mem _ hg₁N n
        rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
          (stab_le_normalizer_zm _ x hks), map_conj_eq_of_mem_normalizer hkN])
      (Subgroup.mem_zpowers _)
  have hconj : ∀ u : ↥(Uloc h.le L x), ∃ hm : (g₁ : (puAmalgam h.le).Universal) * u *
      (g₁ : (puAmalgam h.le).Universal)⁻¹ ∈ Uloc h.le L x,
      natVec hψ ⟨_, hm⟩ = ((B ^ 2 ^ e : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ u := by
    intro u
    have hm : (g₁ : (puAmalgam h.le).Universal) * u * (g₁ : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L x := (Subgroup.mem_normalizer_iff.mp (hUn g₁.2) _).mp u.2
    refine ⟨hm, ?_⟩
    rw [natVec_conj hψ g₁ u ⟨_, hm⟩ rfl, hψg₁]
  have hRU : R' ≤ Uloc h.le L x :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hA'.trans hUn)
  have hRmapU : R'.map (MulAut.conj (g₁ : (puAmalgam h.le).Universal)).toMonoidHom ≤
      Uloc h.le L x :=
    (Subgroup.map_mono hRU).trans (map_conj_eq_of_mem_normalizer (hUn g₁.2)).le
  have hinf : R' ⊓ R'.map (MulAut.conj (g₁ : (puAmalgam h.le).Universal)).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hwR, w', hw'R, rfl⟩
    have hw'U := hRU hw'R
    obtain ⟨c, hc⟩ : ∃ c : F, natVec hψ ⟨w', hw'U⟩ = c • r := by
      have := (hmemR ⟨w', hw'U⟩).mp hw'R
      rw [hℓeq] at this
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
      exact ⟨c, hc.symm⟩
    obtain ⟨hm, hnat⟩ := hconj ⟨w', hw'U⟩
    have hwR' : natVec hψ ⟨_, hm⟩ ∈ F ∙ r := by
      rw [← hℓeq]
      exact (hmemR ⟨_, hm⟩).mp (by simpa [MulAut.conj_apply] using hwR)
    rw [hnat, hc, Matrix.mulVec_smul] at hwR'
    by_cases hc0 : c = 0
    · have h1 : (⟨w', hw'U⟩ : ↥(Uloc h.le L x)) = 1 :=
        natVec_injective hψ (by rw [hc, hc0, zero_smul, natVec_one])
      have hw'1 : w' = 1 := congrArg Subtype.val h1
      rw [hw'1, map_one]
      exact Subgroup.one_mem _
    · exfalso
      apply hBr (2 ^ e) hndvd
      have := Submodule.smul_mem _ c⁻¹ hwR'
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine ⟨(g₁ : (puAmalgam h.le).Universal), g₁.2, hg₁N, by
    rw [← Subgroup.coe_pow, hg₁3, Subgroup.coe_one], fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨u, hu, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hx hz
    have hζc : ζ * (g₁ : (puAmalgam h.le).Universal)⁻¹ = (g₁ : (puAmalgam h.le).Universal)⁻¹ * ζ :=
      (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hx hζ) _
        (Subgroup.inv_mem _ g₁.2)).symm
    have e1 : (g₁ : (puAmalgam h.le).Universal) * (u * ζ) * (g₁ : (puAmalgam h.le).Universal)⁻¹ *
        (u * ζ)⁻¹ = (g₁ : (puAmalgam h.le).Universal) * u * (g₁ : (puAmalgam h.le).Universal)⁻¹ *
          u⁻¹ := by
      calc (g₁ : (puAmalgam h.le).Universal) * (u * ζ) * (g₁ : (puAmalgam h.le).Universal)⁻¹ *
            (u * ζ)⁻¹ = (g₁ : (puAmalgam h.le).Universal) * u *
              (ζ * (g₁ : (puAmalgam h.le).Universal)⁻¹) * ζ⁻¹ * u⁻¹ := by group
        _ = _ := by rw [hζc]; group
    rw [e1]
    obtain ⟨hm, hnat⟩ := hconj ⟨u, hu⟩
    have hmem : ⟨_, hm⟩ * (⟨u, hu⟩ : ↥(Uloc h.le L x))⁻¹ ∈ (⊤ : Subgroup ↥(Uloc h.le L x)) :=
      Subgroup.mem_top _
    have hH : (g₁ : (puAmalgam h.le).Universal) * u * (g₁ : (puAmalgam h.le).Universal)⁻¹ *
        u⁻¹ ∈ ⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ := by
      have := (hmemH (⟨_, hm⟩ * (⟨u, hu⟩ : ↥(Uloc h.le L x))⁻¹)).mpr (by
        rw [natVec_mul, natVec_inv, hnat, ← sub_eq_add_neg]
        exact hBn _ _)
      simpa using this
    have hUZ := h464 x ρ hx hxρ
    rw [Usup, zv_of_isMVtx _ hx] at hUZ
    exact hUZ hH
  · have hRmap : R'.map (MulAut.conj (g₁ : (puAmalgam h.le).Universal)).toMonoidHom ≤
        ⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ :=
      (Subgroup.map_mono hle).trans (map_conj_eq_of_mem_normalizer hg₁H).le
    have : Finite ↥R' := finite_of_le_stab h hx (hRU.trans hUs)
    have : Finite ↥(R'.map (MulAut.conj (g₁ : (puAmalgam h.le).Universal)).toMonoidHom) :=
      finite_of_le_stab h hx (hRmapU.trans hUs)
    have hprod := card_sup_mul_card_inf_of_commute (H := R')
      (K := R'.map (MulAut.conj (g₁ : (puAmalgam h.le).Universal)).toMonoidHom)
      (fun a ha b hb => uloc_comm h hfull hx a (hRU ha) b (hRmapU hb))
    rw [hinf, Subgroup.card_bot, mul_one, Subgroup.card_map_of_injective (MulAut.conj _).injective,
      hcard] at hprod
    have hHcard : Nat.card ↥⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ = Fintype.card F ^ 2 := by
      have := hsq x ρ hx hxρ
      rwa [Usup, zv_of_isMVtx _ hx] at this
    have : Finite ↥⁅ZM (puAmalgam h.le) x, Qv _ ρ⁆ :=
      Nat.finite_of_card_ne_zero (by rw [hHcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge (sup_le hle hRmap) (by rw [hHcard, hprod, sq])
  · exact hinf

include h464 hsq h466 in
theorem exists_transv {y ρ : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hyρ : (puAmalgam h.le).treeGraph.Adj y ρ) {H : Subgroup (puAmalgam h.le).Universal}
    (hH : H ≤ ZH (puAmalgam h.le) ρ) (hcardH : Nat.card H ≤ Fintype.card F ^ 2)
    (hR : Fintype.card F ≤ Nat.card ↥(H ⊓ Zloc h.le L y)) (hnot : ¬ H ≤ Zloc h.le L y) :
    ∃ g : (puAmalgam h.le).Universal, g ∈ stab _ y ∧
      g ∈ Subgroup.normalizer (Qv (puAmalgam h.le) ρ : Set _) ∧
      H.map (MulAut.conj g).toMonoidHom ≠ H ∧
      ∃ K : Subgroup (puAmalgam h.le).Universal, K ≤ Uloc h.le L y ∧
        Nat.card K ≤ Fintype.card F ∧ ∀ z ∈ ZH (puAmalgam h.le) ρ, g * z * g⁻¹ * z⁻¹ ∈ K := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hy
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ y := qv_le_stab_of_adj _ hyρ.symm
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨h2, -⟩ := fixN_natImage_qv h hφ h464 hsq hy hyρ hψ
  set P := fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) with hPdef
  have hUs : Uloc h.le L y ≤ stab _ y := puTrans_le_stab h.le _ y
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) y
  have hZs : Zloc h.le L y ≤ stab _ y := puTrans_le_stab h.le _ y
  have hZc := zloc_le_centralizer_stab h hfull hy
  have hZρZ : ZH (puAmalgam h.le) ρ ≤ ZM _ y := zh_le_zm _ hyρ
  have hZsρ : ZM (puAmalgam h.le) y ≤ stab _ y := (zm_le_qv_self _ hy h.critDist_pos).trans
    (qv_le_stab _ y)
  have hHs : H ≤ stab _ y := hH.trans (hZρZ.trans hZsρ)
  have hZlocρ : Zloc h.le L y ≤ ZH (puAmalgam h.le) ρ := fun z hz =>
    mem_zh_of_mem_zm h hy hyρ (zloc_le_zm h hfull hy hz)
      (Subgroup.centralizer_le hT (hZc hz))
  have hUZ := uloc_inf_zloc h hfull y
  set S := (H ⊔ Zloc h.le L y) ⊓ Uloc h.le L y with hSdef
  have : Finite ↥(Zloc h.le L y) := finite_of_le_stab h hy hZs
  have : Finite ↥H := finite_of_le_stab h hy hHs
  have : Finite ↥S := finite_of_le_stab h hy (inf_le_right.trans hUs)
  have hcommZ : ∀ a ∈ (stab (puAmalgam h.le) y), ∀ b ∈ Zloc h.le L y, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hZc hb) a ha
  have hSZ : S ⊔ Zloc h.le L y = H ⊔ Zloc h.le L y := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le ?_ le_sup_right)
    intro w hw
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hy (hZρZ (hH hw))
    have huS : u ∈ S := by
      refine ⟨?_, hu⟩
      have e : u = (u * ζ) * ζ⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hζ))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huS) (Subgroup.mem_sup_right hζ)
  have hSinf : S ⊓ Zloc h.le L y = ⊥ := by
    rw [eq_bot_iff, ← hUZ]
    exact inf_le_inf_right _ inf_le_right
  have hc1 := card_sup_mul_card_inf_of_commute (H := S) (K := Zloc h.le L y)
    (fun a ha b hb => hcommZ a (hUs ha.2) b hb)
  have hc2 := card_sup_mul_card_inf_of_commute (H := H) (K := Zloc h.le L y)
    (fun a ha b hb => hcommZ a (hHs ha) b hb)
  rw [hSZ, hSinf, Subgroup.card_bot, mul_one] at hc1
  have hZpos : 0 < Nat.card ↥(Zloc h.le L y) := Nat.card_pos
  have hSH : Nat.card ↥S * Nat.card ↥(H ⊓ Zloc h.le L y) = Nat.card ↥H := by
    have e : Nat.card ↥S * Nat.card ↥(H ⊓ Zloc h.le L y) * Nat.card ↥(Zloc h.le L y) =
        Nat.card ↥H * Nat.card ↥(Zloc h.le L y) := by
      rw [← hc2, hc1]; ring
    exact Nat.eq_of_mul_eq_mul_right hZpos e
  have hSq : Nat.card ↥S ≤ Fintype.card F := by
    by_contra hlt
    push Not at hlt
    have h1 : Fintype.card F * Fintype.card F < Nat.card ↥S * Nat.card ↥(H ⊓ Zloc h.le L y) :=
      Nat.mul_lt_mul_of_lt_of_le hlt hR (lt_of_lt_of_le Fintype.card_pos hR)
    rw [hSH] at h1
    nlinarith
  obtain ⟨w, hwH, hwZ⟩ := Set.not_subset.mp hnot
  obtain ⟨u, hu, ζ, hζ, hwu⟩ := exists_uloc_mul_zloc h hfull hy (hZρZ (hH hwH))
  have huS : u ∈ S := by
    refine ⟨?_, hu⟩
    have e : u = w * ζ⁻¹ := by rw [hwu]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwH)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hζ))
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hwZ
    rw [hwu, one_mul]
    exact hζ
  let S' : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ s : ↥(Uloc h.le L y), (s : (puAmalgam h.le).Universal) ∈ S ∧
        natVec hψ s = v}
      add_mem' := by
        rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
        exact ⟨s * s', Subgroup.mul_mem _ hs hs', natVec_mul hψ s s'⟩
      zero_mem' := ⟨1, Subgroup.one_mem _, natVec_one hψ⟩
      neg_mem' := by
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨s⁻¹, Subgroup.inv_mem _ hs, natVec_inv hψ s⟩ }
  have hS'P : ∀ v ∈ S', v ∈ P := by
    rintro _ ⟨s, hs, rfl⟩
    refine (mem_centralizer_iff_natVec hψ hT s).mp ?_
    have hsZ : (s : (puAmalgam h.le).Universal) ∈ ZH (puAmalgam h.le) ρ :=
      (sup_le hH hZlocρ) hs.1
    exact zh_le_centralizer _ ρ hsZ
  have hS'card : Nat.card S' ≤ Nat.card F := by
    have hsurj : Function.Surjective (fun s : ↥S => (⟨natVec hψ ⟨s, s.2.2⟩, ⟨s, s.2.2⟩, s.2,
        rfl⟩ : S')) := by
      rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    calc Nat.card S' ≤ Nat.card ↥S := Nat.card_le_card_of_surjective _ hsurj
      _ ≤ Fintype.card F := hSq
      _ = Nat.card F := Nat.card_eq_fintype_card.symm
  have hv0 : natVec hψ ⟨u, hu⟩ ≠ 0 := by
    intro h0
    apply hu1
    have : (⟨u, hu⟩ : ↥(Uloc h.le L y)) = 1 := natVec_injective hψ (by rw [h0, natVec_one])
    exact congrArg Subtype.val this
  obtain ⟨A, e, hAe, hAP, hAv⟩ := exists_transv_of_plane h2 hS'P hS'card
    ⟨⟨u, hu⟩, huS, rfl⟩ hv0
  obtain ⟨g₀, hg₀⟩ := toSL3_surjective hψs A
  have hg₀N := mem_normalizer_qv_of_toSL3 h hφ h464 hsq h466 hy hyρ hψ (g := g₀)
    (by rw [hg₀]; exact hAP)
  have hconj : ∀ u' : ↥(Uloc h.le L y), ∃ hm : (g₀ : (puAmalgam h.le).Universal) * u' *
      (g₀ : (puAmalgam h.le).Universal)⁻¹ ∈ Uloc h.le L y,
      natVec hψ ⟨_, hm⟩ = ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ u' := by
    intro u'
    have hm : (g₀ : (puAmalgam h.le).Universal) * u' * (g₀ : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L y := (Subgroup.mem_normalizer_iff.mp (hUn g₀.2) _).mp u'.2
    exact ⟨hm, by rw [natVec_conj hψ g₀ u' ⟨_, hm⟩ rfl, hg₀]⟩
  have hζc : ∀ ζ' ∈ Zloc h.le L y, (g₀ : (puAmalgam h.le).Universal) * ζ' *
      (g₀ : (puAmalgam h.le).Universal)⁻¹ = ζ' := fun ζ' hζ' => by
    rw [hcommZ _ g₀.2 _ hζ', mul_inv_cancel_right]
  let K : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {k | ∃ hk : k ∈ Uloc h.le L y, natVec hψ ⟨k, hk⟩ ∈ F ∙ e}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have : natVec hψ ⟨a * b, Subgroup.mul_mem _ ha hb⟩ =
            natVec hψ ⟨a, ha⟩ + natVec hψ ⟨b, hb⟩ := natVec_mul hψ ⟨a, ha⟩ ⟨b, hb⟩
        rw [this]
        exact Submodule.add_mem _ ha' hb'
      one_mem' := ⟨Subgroup.one_mem _, by
        have : natVec hψ ⟨1, Subgroup.one_mem _⟩ = 0 := natVec_one hψ
        rw [this]; exact Submodule.zero_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have : natVec hψ ⟨a⁻¹, Subgroup.inv_mem _ ha⟩ = -natVec hψ ⟨a, ha⟩ :=
          natVec_inv hψ ⟨a, ha⟩
        rw [this]; exact Submodule.neg_mem _ ha' }
  have hKcard : Nat.card K ≤ Fintype.card F := by
    have hinj : Function.Injective (fun k : K => (⟨natVec hψ ⟨k, k.2.1⟩, k.2.2⟩ : ↥(F ∙ e))) := by
      intro k k' hkk
      have h1 : natVec hψ ⟨k, k.2.1⟩ = natVec hψ ⟨k', k'.2.1⟩ := congrArg Subtype.val hkk
      exact Subtype.ext (Subtype.mk.inj (natVec_injective hψ h1))
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h3 : Nat.card ↥(F ∙ e) = Nat.card F ^ Module.finrank F ↥(F ∙ e) :=
      Module.natCard_eq_pow_finrank
    have h2 : Module.finrank F ↥(F ∙ e) ≤ 1 := by
      by_cases he0 : e = 0
      · rw [he0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        omega
      · rw [finrank_span_singleton he0]
    calc Nat.card K ≤ Nat.card F ^ Module.finrank F ↥(F ∙ e) := h3 ▸ h1
      _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right (by omega) h2
      _ = Fintype.card F := by rw [pow_one, Nat.card_eq_fintype_card]
  refine ⟨(g₀ : (puAmalgam h.le).Universal), g₀.2, hg₀N, fun heq => ?_, K, fun k hk => hk.1,
    hKcard, fun z hz => ?_⟩
  ·
    apply hAv
    obtain ⟨hm, hnat⟩ := hconj ⟨u, hu⟩
    have hgw : (g₀ : (puAmalgam h.le).Universal) * w * (g₀ : (puAmalgam h.le).Universal)⁻¹ ∈ H := by
      rw [← heq]
      exact ⟨w, hwH, rfl⟩
    have hgu : (g₀ : (puAmalgam h.le).Universal) * u * (g₀ : (puAmalgam h.le).Universal)⁻¹ ∈ S := by
      refine ⟨?_, hm⟩
      have e1 : (g₀ : (puAmalgam h.le).Universal) * u * (g₀ : (puAmalgam h.le).Universal)⁻¹ =
          ((g₀ : (puAmalgam h.le).Universal) * w * (g₀ : (puAmalgam h.le).Universal)⁻¹) * ζ⁻¹ := by
        rw [hwu]
        have := hζc ζ hζ
        calc (g₀ : (puAmalgam h.le).Universal) * u * (g₀ : (puAmalgam h.le).Universal)⁻¹ =
            (g₀ : (puAmalgam h.le).Universal) * u * (g₀ : (puAmalgam h.le).Universal)⁻¹ *
              ((g₀ : (puAmalgam h.le).Universal) * ζ * (g₀ : (puAmalgam h.le).Universal)⁻¹) *
              ζ⁻¹ := by rw [this]; group
          _ = _ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgw)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hζ))
    exact ⟨⟨_, hm⟩, hgu, hnat⟩
  ·
    obtain ⟨u', hu', ζ', hζ', rfl⟩ := exists_uloc_mul_zloc h hfull hy (hZρZ hz)
    obtain ⟨hm, hnat⟩ := hconj ⟨u', hu'⟩
    have e1 : (g₀ : (puAmalgam h.le).Universal) * (u' * ζ') *
        (g₀ : (puAmalgam h.le).Universal)⁻¹ * (u' * ζ')⁻¹ =
        (g₀ : (puAmalgam h.le).Universal) * u' * (g₀ : (puAmalgam h.le).Universal)⁻¹ * u'⁻¹ := by
      have := hζc ζ' hζ'
      calc (g₀ : (puAmalgam h.le).Universal) * (u' * ζ') *
            (g₀ : (puAmalgam h.le).Universal)⁻¹ * (u' * ζ')⁻¹ =
          (g₀ : (puAmalgam h.le).Universal) * u' * (g₀ : (puAmalgam h.le).Universal)⁻¹ *
            ((g₀ : (puAmalgam h.le).Universal) * ζ' * (g₀ : (puAmalgam h.le).Universal)⁻¹) *
            ζ'⁻¹ * u'⁻¹ := by group
        _ = _ := by rw [this]; group
    rw [e1]
    refine ⟨Subgroup.mul_mem _ hm (Subgroup.inv_mem _ hu'), ?_⟩
    have : natVec hψ ⟨_, Subgroup.mul_mem _ hm (Subgroup.inv_mem _ hu')⟩ =
        natVec hψ ⟨_, hm⟩ + natVec hψ (⟨u', hu'⟩ : ↥(Uloc h.le L y))⁻¹ :=
      natVec_mul hψ ⟨_, hm⟩ (⟨u', hu'⟩ : ↥(Uloc h.le L y))⁻¹
    rw [this, natVec_inv, hnat, ← sub_eq_add_neg]
    exact hAe _

end Vertex

end CFSG.Quasithin.MS93.S46.I466b
