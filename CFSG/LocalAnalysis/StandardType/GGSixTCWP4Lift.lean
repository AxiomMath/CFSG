module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley

section Lift

variable {τ : Tag} {Lf : Type} [Field Lf] {X : Type} [Group X]
  {Γ : Subgroup (ModGL τ Lf)} {G₀ B : Subgroup X} (fr : GGTCUFrame Γ G₀ B)

@[expose] noncomputable def GGTCUFrame.tcLangHom : ↥G₀ →* ModGL τ Lf :=
  fr.embLang.comp (QuotientGroup.mk' (Subgroup.center ↥G₀))

theorem GGTCUFrame.tcLangHom_ker (g : ↥G₀) (hg : fr.tcLangHom g = 1) :
    g ∈ Subgroup.center ↥G₀ := by
  have h1 : (QuotientGroup.mk g : ↥G₀ ⧸ Subgroup.center ↥G₀) = 1 :=
    fr.embLang_injective (by simpa [GGTCUFrame.tcLangHom] using hg)
  exact (QuotientGroup.eq_one_iff g).mp h1

theorem GGTCUFrame.range_tcLangHom : fr.tcLangHom.range = Γ := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact (fr.Θ (QuotientGroup.mk g)).2
  · intro hy
    obtain ⟨z, hz⟩ := fr.Θ.surjective ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨g, congrArg Subtype.val hz⟩

theorem GGTCUFrame.exists_tcComponent_lift {d : X} (hd : d ∈ B) {Kt : Subgroup (ModGL τ Lf)}
    (hK : IsComponentOf Kt (Γ ⊓ Subgroup.centralizer ({fr.toLang ⟨d, hd⟩} : Set (ModGL τ Lf)))) :
    ∃ K : Subgroup X, K ≤ G₀ ∧
      IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({d} : Set X)) ∧ fr.JLang K = Kt := by
  classical
  set ψ := fr.tcLangHom with hψ
  set C : Subgroup ↥G₀ :=
    (Γ ⊓ Subgroup.centralizer ({fr.toLang ⟨d, hd⟩} : Set (ModGL τ Lf))).comap ψ with hC
  have hCmap : C.map ψ = Γ ⊓ Subgroup.centralizer ({fr.toLang ⟨d, hd⟩} : Set (ModGL τ Lf)) := by
    rw [hC, Subgroup.map_comap_eq, hψ, fr.range_tcLangHom]
    exact inf_of_le_right inf_le_left
  have hKb : IsComponentOf Kt (C.map ψ) := by rw [hCmap]; exact hK
  obtain ⟨K₀, hK₀, hK₀map⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift ψ fr.tcLangHom_ker hKb
  set K : Subgroup X := K₀.map G₀.subtype with hKdef
  have hKG : K ≤ G₀ := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hKsub : K.subgroupOf G₀ = K₀ := by
    ext g
    simp only [Subgroup.mem_subgroupOf, hKdef, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, hhg⟩
      exact (Subtype.ext hhg : h = g) ▸ hh
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hJL : fr.JLang K = Kt := by
    unfold GGTCUFrame.JLang
    rw [hKsub, Subgroup.map_map]
    exact hK₀map
  have hKperf : commutator ↥K = ⊤ := by
    have e : ↥K₀ ≃* ↥K := Subgroup.equivMapOfInjective K₀ G₀.subtype Subtype.val_injective
    have hp0 : Group.IsPerfect ↥K₀ := Group.isPerfect_def.mpr hK₀.2.2.1
    exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have hcomm : fr.JLang K ≤ Subgroup.centralizer
      ((fr.DLang (Subgroup.zpowers d) : Subgroup (ModGL τ Lf)) : Set (ModGL τ Lf)) := by
    rw [hJL, fr.centralizer_DLang_zpowers hd]
    exact fun y hy => (hK.1 hy).2
  have hdz : Subgroup.zpowers d ≤ B := Subgroup.zpowers_le.2 hd
  have hDK : Subgroup.zpowers d ≤ Subgroup.centralizer (K : Set X) :=
    fr.le_centralizer_of_lang_commute hdz hKG hKperf hcomm
  have hKd : K ≤ Subgroup.centralizer ({d} : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.1 (hDK (Subgroup.mem_zpowers y)) k hk).symm
  set C₂ : Subgroup ↥G₀ := (Subgroup.centralizer ({d} : Set X)).comap G₀.subtype with hC₂
  have hC₂C : C₂ ≤ C := by
    intro g hg
    rw [hC, Subgroup.mem_comap]
    refine ⟨(fr.Θ (QuotientGroup.mk g)).2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨n, hn1, hn2⟩ := fr.act ⟨d, hd⟩
    have hdg : d * (g : X) = (g : X) * d :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hg) d rfl
    have h1 := hn2 g
    have h2 : (n : X) * g * (n : X)⁻¹ = g := by
      rw [← h1]
      calc d * (g : X) * d⁻¹ = (g : X) * d * d⁻¹ := by rw [hdg]
        _ = g := by group
    have h3 : n * g = g * n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (n : X) * g = (n : X) * g * (n : X)⁻¹ * n := by group
        _ = g * n := by rw [h2]
    have h4 : ψ n = fr.toLang ⟨d, hd⟩ := by
      simp [hψ, GGTCUFrame.tcLangHom, GGTCUFrame.toLang, hn1]
    rw [← h4, ← map_mul, ← map_mul, h3]
  have hK₀C₂ : K₀ ≤ C₂ := fun k hk => hKd ⟨k, hk, rfl⟩
  have hK₀' : IsComponentOf K₀ C₂ :=
    CFSG.Assembly.isComponentOf_iff_open.1
      (CFSG.Assembly.IsComponentOf.of_le_of_le (CFSG.Assembly.isComponentOf_iff_open.2 hK₀)
        hK₀C₂ hC₂C)
  obtain ⟨-, hsub, hq⟩ := hK₀'
  have hmapC₂ : C₂.map G₀.subtype = G₀ ⊓ Subgroup.centralizer ({d} : Set X) := by
    rw [hC₂, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  refine ⟨K, hKG, ⟨le_inf hKG hKd, ?_, ?_⟩, hJL⟩
  · have h := CFSG.Open.IsSubnormal.map G₀.subtype hsub
    rwa [hmapC₂] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.equivMapOfInjective K₀ G₀.subtype Subtype.val_injective).symm hq

@[expose] noncomputable def GGTCUFrame.tcLangRestrict {K : Subgroup X} (hKG : K ≤ G₀) :
    ↥K →* ↥(fr.JLang K) :=
  MonoidHom.codRestrict (fr.tcLangHom.comp (Subgroup.inclusion hKG)) (fr.JLang K)
    fun k => ⟨_, ⟨⟨k, hKG k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩, rfl⟩

theorem GGTCUFrame.tcLangRestrict_apply {K : Subgroup X} (hKG : K ≤ G₀) (k : ↥K) :
    ((fr.tcLangRestrict hKG k : ↥(fr.JLang K)) : ModGL τ Lf) = fr.tcLangHom ⟨k, hKG k.2⟩ :=
  rfl

theorem GGTCUFrame.tcLangRestrict_surjective {K : Subgroup X} (hKG : K ≤ G₀) :
    Function.Surjective (fr.tcLangRestrict hKG) := by
  rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩⟩
  exact ⟨⟨(g : X), Subgroup.mem_subgroupOf.1 hg⟩, Subtype.ext rfl⟩

theorem GGTCUFrame.tcLangRestrict_ker {K : Subgroup X} (hKG : K ≤ G₀) :
    (fr.tcLangRestrict hKG).ker ≤ Subgroup.center ↥K := by
  intro k hk
  have h1 : fr.tcLangHom ⟨k, hKG k.2⟩ = 1 := by
    have h0 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    exact h0
  have h2 := fr.tcLangHom_ker _ h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro g
  have h3 := congrArg Subtype.val (h2 ⟨g, hKG g.2⟩)
  apply Subtype.ext
  simpa using h3

theorem GGTCUFrame.exists_tcCenterQuotEquiv {K : Subgroup X} (hKG : K ≤ G₀)
    (hKperf : commutator ↥K = ⊤) :
    ∃ e : ↥K ⧸ Subgroup.center ↥K ≃* ↥(fr.JLang K) ⧸ Subgroup.center ↥(fr.JLang K),
      ∀ k : ↥K, e (QuotientGroup.mk k) = QuotientGroup.mk (fr.tcLangRestrict hKG k) := by
  have hP : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKperf
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect hP (fr.tcLangRestrict hKG)
    (fr.tcLangRestrict_surjective hKG) (fr.tcLangRestrict_ker hKG)
  let g : ↥K ⧸ Subgroup.center ↥K →* ↥(fr.JLang K) ⧸ Subgroup.center ↥(fr.JLang K) :=
    QuotientGroup.map _ _ (fr.tcLangRestrict hKG) hc.ge
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : fr.tcLangRestrict hKG k ∈ Subgroup.center ↥(fr.JLang K) :=
      (QuotientGroup.eq_one_iff _).1 hq
    have hk : k ∈ Subgroup.center ↥K := by
      rw [← hc]
      exact h1
    exact (QuotientGroup.eq_one_iff k).2 hk
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, rfl⟩ := fr.tcLangRestrict_surjective hKG y
    exact ⟨QuotientGroup.mk k, rfl⟩
  exact ⟨MulEquiv.ofBijective g ⟨hinj, hsurj⟩, fun k => rfl⟩

theorem GGTCUFrame.tcLangHom_conj (b : ↥B) {l l' : ↥G₀}
    (h : (l' : X) = (b : X)⁻¹ * l * b) :
    fr.tcLangHom l' = (fr.toLang b)⁻¹ * fr.tcLangHom l * fr.toLang b := by
  obtain ⟨n, hn1, hn2⟩ := fr.act b
  have h1 : l' = n⁻¹ * l * n := by
    apply Subtype.ext
    have hy := hn2 (n⁻¹ * l * n)
    have h2 : (b : X) * ((n⁻¹ * l * n : ↥G₀) : X) * (b : X)⁻¹ = (l : X) := by
      rw [hy]
      simp [mul_assoc]
    rw [h]
    calc (b : X)⁻¹ * l * b
        = (b : X)⁻¹ * ((b : X) * ((n⁻¹ * l * n : ↥G₀) : X) * (b : X)⁻¹) * b := by rw [h2]
      _ = ((n⁻¹ * l * n : ↥G₀) : X) := by group
  have h3 : fr.tcLangHom n = fr.toLang b := by
    simp [GGTCUFrame.tcLangHom, GGTCUFrame.toLang, hn1]
  rw [h1, map_mul, map_mul, map_inv, h3]


theorem GGTCUFrame.ggInnerDiagOn_of_lang [Finite X] (fr : GGTCUFrame Γ G₀ B) {x : X} (hx : x ∈ B)
    {K : Subgroup X} (hKG : K ≤ G₀) (hKperf : commutator ↥K = ⊤)
    (hKnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set X))
    (h : GGInnerDiagOn (Subgroup.zpowers (fr.toLang ⟨x, hx⟩)) (fr.JLang K)) :
    GGInnerDiagOn (Subgroup.zpowers x) K := by
  obtain ⟨e, he⟩ := fr.exists_tcCenterQuotEquiv hKG hKperf
  unfold GGInnerDiagOn at h ⊢
  obtain ⟨-, lab, hΛ, hraw⟩ := h
  refine ⟨hKperf, lab, hΛ, ?_⟩
  refine CFSG.StandardType.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hsimple, hnonab, θ, hnorm, hind⟩
  refine ⟨hsimple, hnonab, e.trans θ, hKnorm, ?_⟩
  intro b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  obtain ⟨φ, hφI, hφ⟩ := hind (fr.toLang ⟨x, hx⟩ ^ m) (Subgroup.zpow_mem_zpowers _ m)
  refine ⟨φ, hφI, ?_⟩
  intro l l' hrel
  show φ (θ (e (QuotientGroup.mk l))) = θ (e (QuotientGroup.mk l'))
  rw [he l, he l']
  apply hφ
  have hxm : x ^ m ∈ B := zpow_mem hx m
  have hconj := fr.tcLangHom_conj ⟨x ^ m, hxm⟩ (l := ⟨l, hKG l.2⟩) (l' := ⟨l', hKG l'.2⟩)
    (by simpa using hrel)
  have hlang : fr.toLang ⟨x ^ m, hxm⟩ = fr.toLang ⟨x, hx⟩ ^ m := by
    have := map_zpow fr.toLang (⟨x, hx⟩ : ↥B) m
    exact this
  rw [GGTCUFrame.tcLangRestrict_apply, GGTCUFrame.tcLangRestrict_apply, hconj, hlang]

open scoped commutatorElement in
theorem perfect_le_of_le_sup_center {G : Type*} [Group G] {P Q : Subgroup G} (hP : ⁅P, P⁆ = P)
    (h : P ≤ Q ⊔ Subgroup.center G) : P ≤ Q := by
  rw [← hP, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h hg₁)
  obtain ⟨y', hy', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h hg₂)
  have hzc : ∀ a : G, a * z = z * a := fun a => Subgroup.mem_center_iff.1 hz a
  have hzc' : ∀ a : G, a * z' = z' * a := fun a => Subgroup.mem_center_iff.1 hz' a
  have e : ⁅y * z, y' * z'⁆ = ⁅y, y'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc y * z * (y' * z') * (y * z)⁻¹ * (y' * z')⁻¹
        = y * (z * (y' * z')) * z⁻¹ * y⁻¹ * (z'⁻¹ * y'⁻¹) := by group
      _ = y * ((y' * z') * z) * z⁻¹ * y⁻¹ * (z'⁻¹ * y'⁻¹) := by rw [← hzc (y' * z')]
      _ = y * (y' * z') * y⁻¹ * (z'⁻¹ * y'⁻¹) := by group
      _ = y * y' * (z' * y⁻¹) * (z'⁻¹ * y'⁻¹) := by group
      _ = y * y' * (y⁻¹ * z') * (z'⁻¹ * y'⁻¹) := by rw [← hzc' y⁻¹]
      _ = y * y' * y⁻¹ * y'⁻¹ := by group
  rw [e, commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem hy hy') (Q.inv_mem hy)) (Q.inv_mem hy')

open scoped commutatorElement in
theorem GGTCUFrame.tcZpowers_le_normalizer {x : X} (hx : x ∈ B) {K : Subgroup X} (hKG : K ≤ G₀)
    (hKperf : commutator ↥K = ⊤)
    (hnorm : Subgroup.zpowers (fr.toLang ⟨x, hx⟩) ≤
      Subgroup.normalizer ((fr.JLang K : Subgroup (ModGL τ Lf)) : Set (ModGL τ Lf))) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set X) := by
  have hperfK : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKperf
  have core : ∀ b : ↥B, fr.toLang b ∈
      Subgroup.normalizer ((fr.JLang K : Subgroup (ModGL τ Lf)) : Set (ModGL τ Lf)) →
      ∀ k ∈ K, (b : X) * k * (b : X)⁻¹ ∈ K := by
    intro b hb k hk
    obtain ⟨n, hn1, hn2⟩ := fr.act b
    have h3 : fr.tcLangHom n = fr.toLang b := by
      simp [GGTCUFrame.tcLangHom, GGTCUFrame.toLang, hn1]
    set K₀ : Subgroup ↥G₀ := K.subgroupOf G₀ with hK₀
    have hperf0 : Group.IsPerfect ↥K₀ :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKG).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKG).symm.surjective
    have hP : ⁅K₀.map (MulAut.conj n).toMonoidHom, K₀.map (MulAut.conj n).toMonoidHom⁆ =
        K₀.map (MulAut.conj n).toMonoidHom := by
      rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hperf0]
    have hle : K₀.map (MulAut.conj n).toMonoidHom ≤ K₀ ⊔ Subgroup.center ↥G₀ := by
      rintro _ ⟨k', hk', rfl⟩
      have hψk' : fr.tcLangHom k' ∈ fr.JLang K := ⟨_, ⟨k', hk', rfl⟩, rfl⟩
      have hconj : fr.tcLangHom ((MulAut.conj n).toMonoidHom k') =
          fr.toLang b * fr.tcLangHom k' * (fr.toLang b)⁻¹ := by
        simp [map_mul, map_inv, h3]
      have hmem : fr.tcLangHom ((MulAut.conj n).toMonoidHom k') ∈ fr.JLang K := by
        rw [hconj]
        exact (Subgroup.mem_normalizer_iff.1 hb (fr.tcLangHom k')).1 hψk'
      obtain ⟨_, ⟨k₀, hk₀, rfl⟩, hq⟩ := hmem
      refine Subgroup.mem_sup_of_normal_right.2 ⟨k₀, hk₀,
        k₀⁻¹ * (MulAut.conj n).toMonoidHom k', ?_, by simp⟩
      refine fr.tcLangHom_ker _ ?_
      rw [map_mul, map_inv]
      have hq' : fr.tcLangHom k₀ = fr.tcLangHom ((MulAut.conj n).toMonoidHom k') := hq
      rw [hq', inv_mul_cancel]
    have hPK := perfect_le_of_le_sup_center hP hle
    have hk₁ : n * (⟨k, hKG hk⟩ : ↥G₀) * n⁻¹ ∈ K₀ :=
      hPK ⟨⟨k, hKG hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    have h4 := hn2 ⟨k, hKG hk⟩
    rw [h4]
    exact Subgroup.mem_subgroupOf.1 hk₁
  intro b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hB : ∀ m : ℤ, x ^ m ∈ B := fun m => zpow_mem hx m
  have hlang : ∀ m : ℤ, fr.toLang ⟨x ^ m, hB m⟩ = fr.toLang ⟨x, hx⟩ ^ m := fun m =>
    map_zpow fr.toLang (⟨x, hx⟩ : ↥B) m
  have hnm : ∀ m : ℤ, fr.toLang ⟨x ^ m, hB m⟩ ∈
      Subgroup.normalizer ((fr.JLang K : Subgroup (ModGL τ Lf)) : Set (ModGL τ Lf)) := fun m => by
    rw [hlang]
    exact hnorm (Subgroup.zpow_mem_zpowers _ m)
  constructor
  · intro hh
    exact core ⟨x ^ m, hB m⟩ (hnm m) h hh
  · intro hh
    have := core ⟨x ^ (-m), hB (-m)⟩ (hnm (-m)) _ hh
    simpa [zpow_neg, mul_assoc] using this

end Lift

end CFSG.StandardType.TableCRes

end
