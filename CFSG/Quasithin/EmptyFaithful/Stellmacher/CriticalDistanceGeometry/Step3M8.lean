module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3N1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3D
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Proj3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv CFSG.Quasithin.EmptyFaithful.Stellmacher

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conjSub_fixSecIn (g : G) (A L N : Subgroup G) :
    conjSub g (fixSecIn A L N) = fixSecIn (conjSub g A) (conjSub g L) (conjSub g N) := by
  unfold fixSecIn
  rw [conjSub_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩
    refine ⟨mul_mem_conjSub hx, fun a' ha' => ?_⟩
    obtain ⟨a, ha, rfl⟩ := ha'
    have := mul_mem_conjSub (g := g) (hxa a ha)
    convert this using 1
    simp [MulAut.conj_apply]
    group
  · rintro ⟨hy, hya⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_conjSub.mp hy, fun a ha => ?_⟩, by group⟩
    have h1 := hya (g * a * g⁻¹) ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h2 := mem_conjSub.mp h1
    convert h2 using 1
    group

omit [Finite G] in
theorem Ctilde_smul (g : ↥(H ⊔ M)) (ν : Geo H M) :
    Ctilde (g • ν) = conjSub (g : G) (Ctilde ν) := by
  unfold Ctilde
  rw [conjSub_fixSecIn, stab_smul, Zv_smul, Vn_smul, conjSub_oTwoRes]

theorem mem_oTwoRes_sup_of_even {F Q : Subgroup G} {θ : ↥F →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hk : ∀ x : ↥F, θ x = 1 ↔ (x : G) ∈ Q) {f : G}
    (hf : f ∈ F) (hA : θ ⟨f, hf⟩ ∈ alternatingGroup (Fin 5)) : f ∈ oTwoRes F ⊔ Q := by
  obtain ⟨o, hoO, hoθ⟩ := alt_le_img_oTwoRes hθs hA
  have hoF : (o : G) ∈ oTwoRes F := Subgroup.mem_subgroupOf.mp hoO
  have hcf : f * (o : G)⁻¹ ∈ Q := by
    have h1 : θ (⟨f, hf⟩ * o⁻¹) = 1 := by rw [map_mul, map_inv, hoθ]; simp
    have := (hk (⟨f, hf⟩ * o⁻¹)).mp h1
    simpa using this
  have : f = (f * (o : G)⁻¹) * (o : G) := by group
  rw [sup_comm, this]
  exact Subgroup.mul_mem_sup hcf hoF

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem card_fixW_modA5_eight (P : CritPath α β α') (V : VhatData β) {D : Subgroup (Perm (Fin 5))}
    (hD : Nat.card D = 8) : Nat.card (fixW V.M5.modA5 D) = 2 := by
  rcases C.vhat_orth_or_nat_symm P V with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
  · have h := card_fixW_of_iso e D
    have h2 := congrArg (fun p => p.2.1) (profile_sylow orth (Or.inl rfl) hD)
    simp only [profile] at h2
    omega
  · have h := card_fixW_of_iso e D
    have h2 := congrArg (fun p => p.2.1) (profile_sylow nat (Or.inr rfl) hD)
    simp only [profile] at h2
    omega

theorem card_img_Qv_alpha (V : VhatData β) : Nat.card (V.img (Qv α)) = 8 := by
  have hb := C.hb6
  have hβα : β ∈ nbrs α := C.hc.adj
  have hαβ : α ∈ nbrs β := mem_nbrs_comm hβα
  have hQα : Qv α ≤ stab β := Qv_le_stab_of_mem_nbrs C.hA hβα
  have hQβ : Qv β ≤ stab β := pCoreOf_le 2 _
  have hedge := C.Qv_sup_Qv_eq_edge C.hv hβα
  have h1 : V.img (Qv α) = V.img (stab α ⊓ stab β) := by
    rw [← hedge, V.img_sup hQα hQβ, V.img_eq_bot_of_le le_rfl, sup_bot_eq]
  rw [h1, V.card_img inf_le_right, inf_comm]
  exact relIndex_Qv_inf_false C.hA hαβ C.vtype_beta

theorem not_Zv_alpha_le_Ctilde_beta : ¬ Zv α ≤ Ctilde β := by
  intro h
  let V := C.vhatDataBeta
  have hLX : Zv β ≤ Vn β := Zv_le_Vn_self C.hA β
  have := V.norm
  have hV : Vn β ≤ Ctilde β := by
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs (show α ∈ nbrs β from mem_nbrs_comm C.hc.adj) hε
    rw [← hgε, Zv_smul]
    calc conjSub (g : G) (Zv α) ≤ conjSub (g : G) (Ctilde β) := conjSub_mono _ h
      _ = Ctilde β := conjSub_eq_of_mem_normalizer (C.Ctilde_normal β hg)
  apply fixW_alt5_ne_top_of_faithful V.faithful
  rw [eq_top_iff]
  intro u _
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (V.β u)
  exact (V.mem_fixW_alt_iff hLX hx.symm).mpr (hV x.2)

theorem mem_sup_of_comm_Qv_alpha (P : CritPath α β α') {x : G} (hx : x ∈ Vn β)
    (hxq : ∀ q ∈ Qv α, q * x * q⁻¹ * x⁻¹ ∈ Zv β) : x ∈ Ctilde β ⊔ Zv α := by
  let V := C.vhatDataBeta
  have hLX : Zv β ≤ Vn β := Zv_le_Vn_self C.hA β
  have := V.norm
  have hβα : β ∈ nbrs α := C.hc.adj
  have hQα : Qv α ≤ stab β := Qv_le_stab_of_mem_nbrs C.hA hβα
  have hD := C.card_img_Qv_alpha V
  have h2 := C.card_fixW_modA5_eight P V hD
  obtain ⟨w0, hw0m, hw0, hw0u⟩ := exists_unique_ne_one h2
  obtain ⟨z, hzZ, hzC⟩ := IsConcreteLE.not_le_iff_exists.mp C.not_Zv_alpha_le_Ctilde_beta
  have hzV : z ∈ Vn β := Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hβα) hzZ
  have hzq : ∀ q ∈ Qv α, q * z * q⁻¹ * z⁻¹ ∈ Zv β := by
    intro q hq
    have h := comm_Zv_eq_bot_of_le_Qv C.hA (K := Qv α) le_rfl
    have hc : q * z = z * q := by
      have := Subgroup.commutator_mem_commutator hq hzZ
      rw [h, Subgroup.mem_bot, commutatorElement_def] at this
      calc q * z = (q * z * q⁻¹ * z⁻¹) * (z * q) := by group
        _ = z * q := by rw [this, one_mul]
    rw [hc]; simp
  have hfix : ∀ y : G, ∀ hy : y ∈ Vn β, (∀ q ∈ Qv α, q * y * q⁻¹ * y⁻¹ ∈ Zv β) →
      ∀ u : V.M5.W, V.β u = QuotientGroup.mk ⟨y, hy⟩ →
        V.M5.projA5 u ∈ fixW V.M5.modA5 (V.img (Qv α)) := by
    intro y hy hyq u hu d hd
    have hu' : u ∈ fixW V.M5 (V.img (Qv α)) :=
      (secData_mem_fixW_iff V.secData hLX hQα hu).mpr ((X1512.mem_fixSecIn hLX).mpr ⟨hy, hyq⟩)
    rw [V.M5.projA5_act, hu' d hd]
  obtain ⟨uz, huz⟩ := V.secData.surj (QuotientGroup.mk ⟨z, hzV⟩)
  have hzf := hfix z hzV hzq uz huz
  have hz1 : V.M5.projA5 uz ≠ 1 := by
    intro h1
    exact hzC ((V.mem_fixW_alt_iff hLX huz).mp ((V.M5.projA5_eq_one_iff uz).mp h1))
  obtain ⟨ux, hux⟩ := V.secData.surj (QuotientGroup.mk ⟨x, hx⟩)
  have hxf := hfix x hx hxq ux hux
  by_cases hx1 : V.M5.projA5 ux = 1
  · exact Subgroup.mem_sup_left ((V.mem_fixW_alt_iff hLX hux).mp ((V.M5.projA5_eq_one_iff ux).mp hx1))
  · have heq : V.M5.projA5 ux = V.M5.projA5 uz := by
      rcases hw0u _ hxf with h | h
      · exact absurd h hx1
      rcases hw0u _ hzf with h' | h'
      · exact absurd h' hz1
      rw [h, h']
    have h1 : V.M5.projA5 (ux * uz⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have hw : V.β (ux * uz⁻¹) = QuotientGroup.mk (⟨x, hx⟩ * ⟨z, hzV⟩⁻¹ : ↥(Vn β)) := by
      rw [map_mul, map_inv, hux, huz, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hmem := (V.mem_fixW_alt_iff hLX hw).mp ((V.M5.projA5_eq_one_iff _).mp h1)
    have e : x = (x * z⁻¹) * z := by group
    rw [e]
    exact Subgroup.mul_mem_sup (by simpa using hmem) hzZ

theorem Ctilde_le_Vn_nbr_alpha {ν ν' : Geo H M} (hν : ν ∈ nbrs α) (hν' : ν' ∈ nbrs α) :
    Ctilde ν ≤ Vn ν' := by
  have hb := C.hb6
  by_cases hνν : ν = ν'
  · subst hνν; exact fixSecIn_le_sec _ _ _
  let P := C.path
  have hβ : β ∈ nbrs α := C.hc.adj
  have base : ∀ l ∈ nbrs α, l ≠ β → Ctilde β ≤ Vn l := by
    intro l hl hlβ
    have hlγ : l ≠ P.reverse.γ := by rw [P.reverse_γ (by omega)]; exact hlβ
    have := (C.symm P).Ctilde_le_Vn_inf P.reverse hl hlγ
    rw [P.reverse_γ (by omega)] at this
    exact this.trans inf_le_right
  obtain ⟨g, hg, hgβ⟩ := stab_transitive_on_nbrs hβ hν
  have hl : g⁻¹ • ν' ∈ nbrs α := smul_mem_nbrs (inv_mem hg : (↑(g⁻¹) : G) ∈ stab α) hν'
  have hlβ : g⁻¹ • ν' ≠ β := by
    intro h
    apply hνν
    rw [← hgβ, ← h, smul_inv_smul]
  have h1 := base _ hl hlβ
  rw [← hgβ, Ctilde_smul]
  calc conjSub (g : G) (Ctilde β) ≤ conjSub (g : G) (Vn (g⁻¹ • ν')) := conjSub_mono _ h1
    _ = Vn ν' := by rw [← Vn_smul, smul_inv_smul]

theorem exists_even_smul {ν ε ε' : Geo H M} (hν : vtype ν = false) (hε : ε ∈ nbrs ν)
    (hε' : ε' ∈ nbrs ν) :
    ∃ g : ↥(H ⊔ M), (g : G) ∈ stab ν ∧ (g : G) ∈ oTwoRes (stab ν) ⊔ Qv ν ∧ g • ε = ε' := by
  obtain ⟨V⟩ := C.nonempty_vhatData hν
  obtain ⟨h, hh, hhε⟩ := stab_transitive_on_nbrs hε hε'
  by_cases hA : V.ψ ⟨h, hh⟩ ∈ alternatingGroup (Fin 5)
  · exact ⟨h, hh, mem_oTwoRes_sup_of_even V.surj V.ker hh hA, hhε⟩
  · have hD : Nat.card (V.img (stab ν ⊓ stab ε)) = 8 := by
      rw [V.card_img inf_le_left]
      exact relIndex_Qv_inf_false C.hA hε hν
    have hnA : ¬ V.img (stab ν ⊓ stab ε) ≤ alternatingGroup (Fin 5) := by
      intro hle
      have := Subgroup.card_dvd_of_le hle
      rw [hD, card_alternatingGroup_five] at this
      omega
    obtain ⟨d, hdD, hdA⟩ := IsConcreteLE.not_le_iff_exists.mp hnA
    obtain ⟨s, hs, rfl⟩ := hdD
    have hs' := Subgroup.mem_subgroupOf.mp hs
    let h' : ↥(H ⊔ M) := h
    let s' : ↥(H ⊔ M) := ⟨(s : G), stab_le ν s.2⟩
    have hsε : s' • ε = ε := smul_eq_of_mem_stab hs'.2
    have hhs : ((h' * s' : ↥(H ⊔ M)) : G) ∈ stab ν := (stab ν).mul_mem hh s.2
    refine ⟨h' * s', hhs, ?_, ?_⟩
    · refine mem_oTwoRes_sup_of_even V.surj V.ker hhs ?_
      rw [Equiv.Perm.mem_alternatingGroup] at hA hdA ⊢
      have e : (⟨((h' * s' : ↥(H ⊔ M)) : G), hhs⟩ : ↥(stab ν)) = ⟨h, hh⟩ * s := rfl
      rw [e, map_mul, map_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (V.ψ ⟨h, hh⟩)) with h1 | h1
      · exact absurd h1 hA
      rcases Int.units_eq_one_or (Equiv.Perm.sign (V.ψ s)) with h2 | h2
      · exact absurd h2 hdA
      rw [h1, h2]; decide
    · rw [mul_smul, hsε]; exact hhε

theorem Zv_beta_sup_zpowers {z : G} (hz : z ∈ Zv α) (hzβ : z ∉ Zv β) :
    Zv β ⊔ Subgroup.zpowers z = Zv α := by
  have hβα : β ∈ nbrs α := C.hc.adj
  set T : Subgroup G := Zv β ⊔ Subgroup.zpowers z with hT
  have hle : T ≤ Zv α :=
    sup_le (C.Zv_le_Zv_of_mem_nbrs C.hv hβα) (Subgroup.zpowers_le.mpr hz)
  have h2 := C.card_Zv_false C.vtype_beta
  have h4 := C.card_Zv_true C.hv
  have hd1 : 2 ∣ Nat.card T := by
    rw [← h2]; exact Subgroup.card_dvd_of_le le_sup_left
  have hc4 : Nat.card T ≤ 4 := by
    rw [← h4]; exact Subgroup.card_le_of_le hle
  have hne : Nat.card T ≠ 2 := by
    intro h
    have heq : Zv β = T :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h2, h])
    exact hzβ (by rw [heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hpos : 0 < Nat.card T := Nat.card_pos
  have h44 : Nat.card T = 4 := by omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h4, h44])

theorem exists_complement (hU : ∀ ν ∈ nbrs α, ⁅Ctilde ν, Qv α⁆ = ⊥) :
    ∃ K' : Subgroup G, K' ≤ Ctilde β ⊔ Zv α ∧ stab α ≤ Subgroup.normalizer (K' : Set G) ∧
      Zv α ⊓ K' = ⊥ ∧ Zv α ⊔ K' = Ctilde β ⊔ Zv α := by
  have hβα : β ∈ nbrs α := C.hc.adj
  have hαβ : α ∈ nbrs β := mem_nbrs_comm hβα
  have hcomm1 : ∀ ν : Geo H M, ν ∈ nbrs α → ∀ x ∈ Ctilde ν, ∀ q ∈ Qv α, q * x * q⁻¹ * x⁻¹ = 1 := by
    intro ν hν x hx q hq
    have h := Subgroup.commutator_mem_commutator hq hx
    rw [Subgroup.commutator_comm, hU ν hν] at h
    simpa [commutatorElement_def] using h
  have hCV : Ctilde β ≤ Vn β := fixSecIn_le_sec _ _ _
  have hZV : Zv α ≤ Vn β := Zv_le_Vn_of_mem_nbrs hαβ
  have hVab := C.isElemAbelian_Vn' β
  have hCZ : ∀ c ∈ Ctilde β, ∀ z ∈ Zv α, c * z = z * c := fun c hc z hz =>
    isMulCommutative_subgroup_iff.mp hVab.1 c (hCV hc) z (hZV hz)
  have hCcent : Ctilde β ≤ Subgroup.normalizer (Zv α : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => (hCZ c hc z hz).symm)
  have hK2V : Ctilde β ⊔ Zv α ≤ Vn β := sup_le hCV hZV
  have hK2ab : IsElemAbelian 2 (Ctilde β ⊔ Zv α) :=
    ⟨isMulCommutative_subgroup_iff.mpr fun x hx y hy =>
      isMulCommutative_subgroup_iff.mp hVab.1 x (hK2V hx) y (hK2V hy),
     fun x hx => hVab.2 x (hK2V hx)⟩
  have hsub : ∀ ν ∈ nbrs α, Ctilde ν ≤ Ctilde β ⊔ Zv α := by
    intro ν hν x hx
    refine C.mem_sup_of_comm_Qv_alpha C.path (C.Ctilde_le_Vn_nbr_alpha hν hβα hx) ?_
    intro q hq
    rw [hcomm1 ν hν x hx q hq]
    exact one_mem _
  have hN : stab α ≤ Subgroup.normalizer ((Ctilde β ⊔ Zv α : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun g hg k hk => ?_
    obtain ⟨c, hc, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hCcent k hk
    let g' : ↥(H ⊔ M) := ⟨g, stab_le α hg⟩
    have hgβ : g' • β ∈ nbrs α := smul_mem_nbrs hg hβα
    have hc' : g * c * g⁻¹ ∈ Ctilde (g' • β) := by
      rw [Ctilde_smul]; exact mul_mem_conjSub hc
    have hz' : g * z * g⁻¹ ∈ Zv α := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA α hg) z).mp hz
    have e : g * (c * z) * g⁻¹ = (g * c * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hsub _ hgβ hc') (Subgroup.mem_sup_right hz')
  have hQK : Qv α ≤ Subgroup.centralizer ((Ctilde β ⊔ Zv α : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨c, hc, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hCcent k hk
    have h1 := hcomm1 β hβα c hc q hq
    have h2 := comm_Zv_eq_bot_of_le_Qv C.hA (K := Qv α) le_rfl
    have hqz : q * z = z * q := by
      have := Subgroup.commutator_mem_commutator hq hz
      rw [h2, Subgroup.mem_bot, commutatorElement_def] at this
      calc q * z = (q * z * q⁻¹ * z⁻¹) * (z * q) := by group
        _ = z * q := by rw [this, one_mul]
    have hqc : q * c = c * q := by
      calc q * c = (q * c * q⁻¹ * c⁻¹) * (c * q) := by group
        _ = c * q := by rw [h1, one_mul]
    calc c * z * q = c * (z * q) := by group
      _ = c * (q * z) := by rw [hqz]
      _ = (c * q) * z := by group
      _ = (q * c) * z := by rw [hqc]
      _ = q * (c * z) := by group
  obtain ⟨ψ, hψ, hker⟩ := exists_quotHom_true C.hA C.hv
  refine exists_normal_complement_nat3 (stab α) (Qv α) (Ctilde β ⊔ Zv α) (Zv α) ψ hψ hker hK2ab hN hQK
    le_sup_right (stab_le_normalizer_Zv C.hA α) (C.card_Zv_true C.hv) ?_
  intro x hx hxz
  have hc := centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true C.hv)
  rw [← hc]
  refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have := hxz z hz
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem Ctilde_beta_eq_Zv (hU : ∀ ν ∈ nbrs α, ⁅Ctilde ν, Qv α⁆ = ⊥) :
    Ctilde β = Zv β := by
  have hb := C.hb6
  let P := C.path
  have hβα : β ∈ nbrs α := C.hc.adj
  have hαβ : α ∈ nbrs β := mem_nbrs_comm hβα
  have hvβ := C.vtype_beta
  obtain ⟨K', hK'K, hK'N, hdisj, hsup⟩ := C.exists_complement hU
  have hCV : Ctilde β ≤ Vn β := fixSecIn_le_sec _ _ _
  have hZβC : Zv β ≤ Ctilde β := C.Zv_le_Ctilde β
  have hK'Q : ∀ ν ∈ nbrs α, ∀ q ∈ Qv ν, ∀ k ∈ K', q * k = k * q := by
    intro ν hν q hq k hk
    have hvν := vtype_false_of_mem_nbrs_true hν C.hv
    have hkK : k ∈ Ctilde β ⊔ Zv α := hK'K hk
    have hkV : k ∈ Vn ν := by
      have : Ctilde β ⊔ Zv α ≤ Vn ν :=
        sup_le (C.Ctilde_le_Vn_nbr_alpha hβα hν) (Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hν))
      exact this hkK
    have hqα : q ∈ stab α := Qv_le_stab_of_mem_nbrs C.hA (mem_nbrs_comm hν) hq
    have h1 : q * k * q⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hK'N hqα) k).mp hk
    have h2 : q * k * q⁻¹ * k⁻¹ ∈ K' := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hk)
    have h3 : q * k * q⁻¹ * k⁻¹ ∈ Zv α := by
      have := Subgroup.commutator_mem_commutator hq hkV
      rw [Subgroup.commutator_comm, C.comm_Vn_Qv_eq hvν] at this
      exact C.Zv_le_Zv_of_mem_nbrs C.hv hν this
    have h4 : q * k * q⁻¹ * k⁻¹ ∈ Zv α ⊓ K' := ⟨h3, h2⟩
    rw [hdisj, Subgroup.mem_bot] at h4
    calc q * k = (q * k * q⁻¹ * k⁻¹) * (k * q) := by group
      _ = k * q := by rw [h4, one_mul]
  by_cases hKC : K' ≤ Ctilde β
  ·
    have hK'bot : K' = ⊥ := by
      have hVQ : Vn β ≤ Qv α := (C.symm P).Vn_le_Qv_alpha' hβα
      have hK'V : K' ≤ Vn β := hKC.trans hCV
      refine eq_bot_of_normalizer_transitive_vertex C.hA
        (show (graph (H ⊔ M) H M).Adj β α from hαβ) ?_ ?_ ?_
      · exact le_inf ((hK'V.trans (Vn_le_Qv' C.hb2 β)).trans (pCoreOf_le 2 _))
          ((hK'V.trans hVQ).trans (pCoreOf_le 2 _))
      · intro ε hε ε' hε'
        obtain ⟨g, hg, hgE, hgε⟩ := C.exists_even_smul hvβ hε hε'
        refine ⟨g, ?_, smul_eq_of_mem_stab hg, hgε⟩
        refine Subgroup.centralizer_le_normalizer _ ?_
        have hE : oTwoRes (stab β) ⊔ Qv β ≤ Subgroup.centralizer (K' : Set G) := by
          refine sup_le ?_ (fun q hq => Subgroup.mem_centralizer_iff.mpr fun k hk =>
            (hK'Q β hβα q hq k hk).symm)
          have h := C.comm_Ctilde_oTwoRes hvβ
          rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
          exact fun o ho => Subgroup.mem_centralizer_iff.mpr fun k hk =>
            Subgroup.mem_centralizer_iff.mp (h ho) k (hKC hk)
        exact hE hgE
      · intro ε hε ε' hε'
        obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
        exact ⟨g, hK'N hg, smul_eq_of_mem_stab hg, hgε⟩
    rw [hK'bot, sup_bot_eq] at hsup
    have hCZ : Ctilde β ≤ Zv α := by rw [hsup]; exact le_sup_left
    refine le_antisymm (fun x hx => ?_) hZβC
    by_contra hxβ
    have hxα := hCZ hx
    have := C.Zv_beta_sup_zpowers hxα hxβ
    apply C.not_Zv_alpha_le_Ctilde_beta
    rw [← this]
    exact sup_le hZβC ((Subgroup.zpowers_le).mpr hx)
  ·
    exfalso
    obtain ⟨k', hk'K', hk'C⟩ := IsConcreteLE.not_le_iff_exists.mp hKC
    have hk'K2 : k' ∈ Ctilde β ⊔ Zv α := hK'K hk'K'
    have hZV : Zv α ≤ Vn β := Zv_le_Vn_of_mem_nbrs hαβ
    have hVab := C.isElemAbelian_Vn' β
    have hCcent : Ctilde β ≤ Subgroup.normalizer (Zv α : Set G) := fun c hc =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (isMulCommutative_subgroup_iff.mp hVab.1 c (hCV hc) z (hZV hz)).symm)
    obtain ⟨x, hx, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hCcent k' hk'K2
    have hzβ : z ∉ Zv β := fun h => hk'C (Subgroup.mul_mem _ hx (hZβC h))
    have hZZ := C.Zv_beta_sup_zpowers hz hzβ
    have hdist : dist α' β < bMin H M := by
      have := C.hc.dist_eq'
      rw [CosetGeom.dist_comm]; omega
    have hZα'β : Zv α' ≤ Qv β := Zv_le_Qv_of_dist_lt_bMin hdist
    obtain ⟨q, hqZ, hqz⟩ : ∃ q ∈ Zv α', q * z ≠ z * q := by
      by_contra hno
      push Not at hno
      apply C.hcomm
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hZZ]
      refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun q hq => hno q hq))
      have h := comm_Zv_eq_bot_of_le_Qv C.hA hZα'β
      have := Subgroup.commutator_mem_commutator hq ha
      rw [h, Subgroup.mem_bot, commutatorElement_def] at this
      calc q * a = (q * a * q⁻¹ * a⁻¹) * (a * q) := by group
        _ = a * q := by rw [this, one_mul]
    have hqQβ : q ∈ Qv β := hZα'β hqZ
    have hp2 : P.p 2 ∈ nbrs β := by
      have h1 : P.p 1 ∈ nbrs (P.p 2) := P.isGeodesic.mem_nbrs_pred (i := 1) (by omega)
      rw [P.p_one] at h1
      exact mem_nbrs_comm h1
    obtain ⟨g, hgs, hgE, hgα⟩ := C.exists_even_smul hvβ hαβ hp2
    generalize hg0 : (g : G) = g0 at hgs hgE
    have hoN : oTwoRes (stab β) ≤ Subgroup.normalizer (Qv β : Set G) :=
      (oTwoRes_le _).trans (le_normalizer_pCoreOf 2 (stab β))
    obtain ⟨o, ho, r, hr, hgor⟩ := exists_mul_of_mem_sup_of_le_normalizer hoN _ hgE
    have hxo : o * x * o⁻¹ = x := by
      have h := C.comm_Ctilde_oTwoRes hvβ
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have := Subgroup.mem_centralizer_iff.mp (h hx) o ho
      rw [mul_inv_eq_iff_eq_mul]; exact this
    have hζ : r * x * r⁻¹ * x⁻¹ ∈ Zv β := by
      have := Subgroup.commutator_mem_commutator hr (hCV hx)
      rw [Subgroup.commutator_comm, C.comm_Vn_Qv_eq hvβ] at this
      exact this
    have hoζ : o * (r * x * r⁻¹ * x⁻¹) * o⁻¹ = r * x * r⁻¹ * x⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hvβ hζ).2 o
        ((oTwoRes_le _) ho)
      rw [mul_inv_eq_iff_eq_mul]; exact this
    have hgx : g0 * x * g0⁻¹ = (r * x * r⁻¹ * x⁻¹) * x := by
      rw [hgor]
      calc o * r * x * (o * r)⁻¹ = o * ((r * x * r⁻¹ * x⁻¹) * x) * o⁻¹ := by group
        _ = (o * (r * x * r⁻¹ * x⁻¹) * o⁻¹) * (o * x * o⁻¹) := by group
        _ = _ := by rw [hoζ, hxo]
    have hw : g0 * z * g0⁻¹ ∈ Zv (P.p 2) := by
      have h1 : g0 * z * g0⁻¹ ∈ conjSub g0 (Zv α) := mul_mem_conjSub hz
      have h2 : Zv (P.p 2) = conjSub g0 (Zv α) := by rw [← hgα, Zv_smul, hg0]
      rw [h2]; exact h1
    have hp2d : dist α' (P.p 2) < bMin H M := by
      have := P.dist_end (j := 2) (by omega)
      rw [CosetGeom.dist_comm]; omega
    have hqp2 : q ∈ Qv (P.p 2) := Zv_le_Qv_of_dist_lt_bMin hp2d hqZ
    have hwq : q * (g0 * z * g0⁻¹) = (g0 * z * g0⁻¹) * q :=
      Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv C.hA (P.p 2) hw).2 q hqp2
    have hζq : q * (r * x * r⁻¹ * x⁻¹) = (r * x * r⁻¹ * x⁻¹) * q :=
      Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv C.hA β hζ).2 q hqQβ
    have hk'q : q * (x * z) = (x * z) * q := hK'Q β hβα q hqQβ (x * z) hk'K'
    have hq' : g0⁻¹ * q * g0 ∈ Qv β := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (stab β) (inv_mem hgs)) q).mp hqQβ
      have h' : g0⁻¹ * q * g0 ∈ pCoreOf 2 (stab β) := by simpa using this
      exact h'
    have hk'q' := hK'Q β hβα _ hq' (x * z) hk'K'
    have hgk : q * (g0 * (x * z) * g0⁻¹) = (g0 * (x * z) * g0⁻¹) * q := by
      calc q * (g0 * (x * z) * g0⁻¹) = g0 * ((g0⁻¹ * q * g0) * (x * z)) * g0⁻¹ := by group
        _ = g0 * ((x * z) * (g0⁻¹ * q * g0)) * g0⁻¹ := by rw [hk'q']
        _ = _ := by group
    have e1 : g0 * (x * z) * g0⁻¹ = ((r * x * r⁻¹ * x⁻¹) * x) * (g0 * z * g0⁻¹) := by
      rw [← hgx]; group
    have hcx : Commute q x := by
      have h1 : Commute q (((r * x * r⁻¹ * x⁻¹) * x) * (g0 * z * g0⁻¹)) := by rw [← e1]; exact hgk
      have h2 : Commute q (r * x * r⁻¹ * x⁻¹) := hζq
      have h3 : Commute q (g0 * z * g0⁻¹) := hwq
      have e2 : x = (r * x * r⁻¹ * x⁻¹)⁻¹ * (((r * x * r⁻¹ * x⁻¹) * x) * (g0 * z * g0⁻¹)) *
          (g0 * z * g0⁻¹)⁻¹ := by group
      rw [e2]
      exact ((h2.inv_right).mul_right h1).mul_right h3.inv_right
    have hcz : Commute q z := by
      have e3 : z = x⁻¹ * (x * z) := by group
      rw [e3]
      exact hcx.inv_right.mul_right hk'q
    exact hqz hcz

theorem Ctilde_eq_Zv
    (hU1 : ∀ ν : Geo H M, vtype ν = false → ∀ ξ ∈ nbrs ν, ⁅Ctilde ν, Qv ξ⁆ = ⊥)
    {ν : Geo H M} (hν : vtype ν = false) : Ctilde ν = Zv ν := by
  have hU : ∀ μ ∈ nbrs α, ⁅Ctilde μ, Qv α⁆ = ⊥ := fun μ hμ =>
    hU1 μ (vtype_false_of_mem_nbrs_true hμ C.hv) α (mem_nbrs_comm hμ)
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := β) (δ' := ν) (by rw [C.vtype_beta, hν])
  rw [Ctilde_smul, C.Ctilde_beta_eq_Zv hU, Zv_smul]

theorem Ctilde_γ_eq_Zv
    (hU1 : ∀ ν : Geo H M, vtype ν = false → ∀ ξ ∈ nbrs ν, ⁅Ctilde ν, Qv ξ⁆ = ⊥)
    (P : CritPath α β α') : Ctilde P.γ = Zv P.γ :=
  C.Ctilde_eq_Zv hU1 (C.vtype_γ P)

end Step3Ctx

end F53.Stellmacher
end CFSG.Quasithin
