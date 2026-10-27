module

public import CFSG.RankThree.PartOne.KF.ToralIso
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.Reduction123
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.SymCtxQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G] [Finite G]

theorem Table123SU5.maximal {p : ℕ} {L A₀ F : Subgroup G} (h : Table123SU5 p L A₀ F) :
    ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F := by
  intro F' hF'L hexp hcomm hFF'
  have hc : IsMulCommutative F' := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have hel : IsElementaryAbelian p F' :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => Subtype.ext (hexp _ g.2)⟩
  refine h.F_max F' hF'L hel ?_ hFF'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm a (hFF' (h.A₀_le_F ha)) x hx

theorem Table123SU5.F_exp {p : ℕ} {L A₀ F : Subgroup G} (h : Table123SU5 p L A₀ F) :
    ∀ f ∈ F, f ^ p = 1 := fun f hf => by
  have := h.F_elem
  exact elemPow_eq_one_of_isElementaryAbelian f hf

theorem Table123SU5.F_comm {p : ℕ} {L A₀ F : Subgroup G} (h : Table123SU5 p L A₀ F) :
    ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.F_elem.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_r11ctx {L A₀ F : Subgroup G} (h : Table123SU5 5 L A₀ F) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f ∧
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) ∧ Nonempty (SymCtx 5 5 K L F) := by
  classical
  obtain ⟨f, hf1, hmod⟩ := h.model
  have hmod' := hmod
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have : Group.IsPerfect ↥L := h.quasisimple.1
  obtain ⟨h5, ⟨ψ₀⟩⟩ := KFSU5.exists_su5_iso h.center_card hf1 hK e
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5 := by
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
    have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
    exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  obtain ⟨ζ, hζ'⟩ := hζ
  have hFexp : ∀ x ∈ F.subgroupOf L, x ^ 5 = 1 := by
    intro x hx
    apply Subtype.ext
    simpa using h.F_exp _ (Subgroup.mem_subgroupOf.mp hx)
  have hFcomm : ∀ x ∈ F.subgroupOf L, ∀ y ∈ F.subgroupOf L, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact h.F_comm _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_five h5 ψ₀ (F.subgroupOf L) hFexp
    hFcomm
  have hTM : torusSU 5 5 K ≤ unitarySU 2 f K 5 := torusSU_le_unitarySU hU h5
  have hψ' := eq_image_torus_of_maximal ψ h.F_le
    (fun m hm => hψ m (Subgroup.mem_subgroupOf.mpr hm)) h.maximal
  have hdist : ∀ i j : Fin 5, i ≠ j → ∃ x ∈ torusSU 5 5 K, ent x i i ≠ ent x j j := fun i j hij =>
    torusSU_char_distinct hζ'.pow_eq_one
      (hζ'.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)) hij
  obtain ⟨SM⟩ := SymCtx.ofMatrixGroup (p := 5) (unitarySU 2 f K 5) hTM
    (fun σ => permGL_mem_unitarySU hU σ) hdist
  obtain ⟨S⟩ := SymCtx.ofIso SM ψ h.F_le h.F_exp hψ'
  exact ⟨f, K, hKf, hKfin, hf1, h5, hmod', ⟨ζ, hζ'⟩, ⟨S⟩⟩

theorem kf123Row11 : KF123Row11 := by
  intro G _ _ p L A₀ F h
  have hp5 := h.p_eq
  subst hp5
  obtain ⟨f, K, hKf, hKfin, hf1, h5, hmodel, hζ, ⟨S⟩⟩ := exists_r11ctx h
  have hp : Nat.Prime 5 := Nat.prime_five
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hcard : Nat.card S.scalarImage = 5 := by
    have hinj : Function.Injective (F.subtype.comp S.tor.toMonoidHom) := fun a b hab =>
      S.tor.injective (Subtype.ext hab)
    rw [SymCtx.scalarImage, Subgroup.card_map_of_injective hinj]
    exact card_scalarSub hp (by norm_num) (dvd_refl 5) hζ
  have hZcard : Nat.card ((Subgroup.center ↥L).map L.subtype) = 5 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact h.center_card
  have hZle : (Subgroup.center ↥L).map L.subtype ≤ S.scalarImage := by
    rintro _ ⟨c, hc, rfl⟩
    have hcF : (c : G) ∈ F := h.A₀_le_F (h.center_le ⟨c, hc, rfl⟩)
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨(c : G), hcF⟩
    refine ⟨d, ?_, congrArg Subtype.val hd⟩
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt (Equiv.swap i j)
      have h1 : g * (c : G) * g⁻¹ = (c : G) := by
        have := Subgroup.mem_center_iff.mp hc ⟨g, hgL⟩
        have h2 : g * (c : G) = (c : G) * g := congrArg Subtype.val this
        rw [h2]
        group
      have h3 : ((S.tor (symAct 5 K (Equiv.swap i j) d) : F) : G) = g * (c : G) * g⁻¹ := by
        rw [← S.act_apply, S.act_eq, ← hgσ, hd]
        rfl
      rw [h1] at h3
      have h4 : symAct 5 K (Equiv.swap i j) d = d :=
        S.tor.injective (Subtype.ext (h3.trans (congrArg Subtype.val hd).symm))
      have h5 := congrFun (congrArg Subtype.val h4) i
      rw [coe_symAct, Equiv.symm_swap, Equiv.swap_apply_left] at h5
      exact h5.symm
  have hZ : (Subgroup.center ↥L).map L.subtype = S.scalarImage :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hcard, hZcard])
  refine ⟨⟨rfl, h.center_card, f, hf1, h5, hmodel⟩, S.card_F (m := 4) rfl hp.pos hζ,
    ⟨S.weylEquiv hp hp2 hζ⟩, S.torusImage_eq_closure hp hp2 hζ,
    fun h11 => absurd rfl h11, fun _ B hBF hB => ?_⟩
  rcases S.torusInvariant_cases hp B hBF hB with hle | hF
  · rw [← hZ] at hle
    have hdvd : Nat.card B ∣ 5 := hZcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h5'
    · exact Or.inl (Subgroup.card_eq_one.mp h1)
    · exact Or.inr (Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, h5'])))
  · exact Or.inr (Or.inr hF)

theorem kf123NTRow11 : KF123NTRow11 := by
  intro G _ _ p L A₀ F h y hyL hyF
  have hp5 := h.p_eq
  subst hp5
  obtain ⟨f, K, hKf, hKfin, hf1, h5, hmodel, hζ, ⟨S⟩⟩ := exists_r11ctx h
  have hpowF : ∀ a : F, a ^ 5 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection_of Nat.prime_five (by norm_num) (by norm_num) hζ
    (fun α hα ht => perm_five_aut_inner α hα ht) (fun π hπ => perm_five_cycle π hπ) hpowF hyL hyF

end CFSG.RankThree.PartOne
