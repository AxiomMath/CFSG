module

public import CFSG.Quasithin.Background.B1MoreTenA

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

section Group

variable {Ω : Type*} [Group Ω]

theorem conj_mem_sup_of_conj_mem {Y Z : Subgroup Ω}
    (hZY : Z ≤ Subgroup.normalizer (Y : Set Ω)) {a : Ω} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    (haZ : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z) : ∀ x ∈ Y ⊔ Z, a * x * a⁻¹ ∈ Y ⊔ Z := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZY).1 hx
  have e : a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (haY y hy) (haZ z hz)

theorem commutator_mem_of_commute_mod {F : Subgroup Ω} {f f' k k' : Ω} (hf : f ∈ F) (hf' : f' ∈ F)
    (hkF : ∀ g ∈ F, k * g * k⁻¹ ∈ F) (hk'F : ∀ g ∈ F, k' * g * k'⁻¹ ∈ F)
    (hkk' : k * k' = k' * k) :
    (f * k) * (f' * k') * (f * k)⁻¹ * (f' * k')⁻¹ ∈ F := by
  have hxx : (f * k) * (f' * k') = (f * (k * f' * k⁻¹)) * (k * k') := by group
  have hyy : (f' * k') * (f * k) = (f' * (k' * f * k'⁻¹)) * (k * k') := by
    have : (f' * k') * (f * k) = (f' * (k' * f * k'⁻¹)) * (k' * k) := by group
    rw [this, ← hkk']
  have e : (f * k) * (f' * k') * (f * k)⁻¹ * (f' * k')⁻¹ =
      ((f * k) * (f' * k')) * ((f' * k') * (f * k))⁻¹ := by group
  rw [e, hxx, hyy]
  have e2 : (f * (k * f' * k⁻¹)) * (k * k') * ((f' * (k' * f * k'⁻¹)) * (k * k'))⁻¹ =
      (f * (k * f' * k⁻¹)) * (f' * (k' * f * k'⁻¹))⁻¹ := by group
  rw [e2]
  exact F.mul_mem (F.mul_mem hf (hkF f' hf')) (F.inv_mem (F.mul_mem hf' (hk'F f hf)))

theorem perfect_le_of_nilpotent_quotient {N F M K : Subgroup Ω} (hFN : F ≤ N) (hMN : M ≤ N)
    (hMn : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hKN : K ≤ N) (hKFM : K ≤ F ⊔ M)
    [Group.IsNilpotent ↥F] (hK : Group.IsPerfect ↥K) : K ≤ M := by
  have hMnorm : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hMN).2 fun m n hm hn => hMn n hn m hm
  let φ : ↥N →* ↥N ⧸ M.subgroupOf N := QuotientGroup.mk' _
  let Fn : Subgroup ↥N := F.subgroupOf N
  let Kn : Subgroup ↥N := K.subgroupOf N
  have hFnil : Group.IsNilpotent ↥Fn :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hFN)).mpr inferInstance
  have hFimg : Group.IsNilpotent ↥(Fn.map φ) :=
    Group.nilpotent_of_surjective (φ.subgroupMap Fn) (φ.subgroupMap_surjective Fn)
  have hKnperf : Group.IsPerfect ↥Kn :=
    Group.IsPerfect.ofSurjective (G := ↥K) (G' := ↥Kn)
      (f := (Subgroup.subgroupOfEquivOfLe hKN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKN).symm.surjective
  have hKle : Kn.map φ ≤ Fn.map φ := by
    rintro _ ⟨k, hk, rfl⟩
    have hkK : (k : Ω) ∈ K := hk
    have hFM : (k : Ω) ∈ M ⊔ F := by rw [sup_comm]; exact hKFM hkK
    have hFnM : F ≤ Subgroup.normalizer (M : Set Ω) := fun f hf => by
      rw [Subgroup.mem_normalizer_iff]
      intro m
      refine ⟨fun hm => hMn f (hFN hf) m hm, fun hm => ?_⟩
      have h2 := hMn f⁻¹ (N.inv_mem (hFN hf)) _ hm
      have e : f⁻¹ * (f * m * f⁻¹) * f⁻¹⁻¹ = m := by group
      rw [e] at h2
      exact h2
    obtain ⟨m, hm, f, hf, hkmf⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hFnM).1 hFM
    refine ⟨⟨f, hFN hf⟩, hf, ?_⟩
    have hmk : (⟨m, hMN hm⟩ : ↥N) ∈ M.subgroupOf N := hm
    have : (k : ↥N) = ⟨m, hMN hm⟩ * ⟨f, hFN hf⟩ := Subtype.ext hkmf
    have hφm : φ ⟨m, hMN hm⟩ = 1 := (QuotientGroup.eq_one_iff (N := M.subgroupOf N) _).2 hmk
    show φ ⟨f, hFN hf⟩ = φ k
    rw [this, map_mul, hφm, one_mul]
  have hKsolv : Group.IsSolvable ↥(Kn.map φ) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKle)
      (Subgroup.inclusion_injective hKle)
  have hKperf' : Group.IsPerfect ↥(Kn.map φ) :=
    Group.IsPerfect.ofSurjective (G := ↥Kn) (G' := ↥(Kn.map φ))
      (f := φ.subgroupMap Kn) (φ.subgroupMap_surjective Kn)
  have hsub : Subsingleton ↥(Kn.map φ) := by
    by_contra h
    have : Nontrivial ↥(Kn.map φ) := not_subsingleton_iff_nontrivial.1 h
    exact Group.IsPerfect.not_isSolvable _ hKsolv
  have hbot : Kn.map φ = ⊥ := Subgroup.eq_bot_of_subsingleton _
  intro k hk
  have h1 : φ ⟨k, hKN hk⟩ ∈ Kn.map φ := ⟨⟨k, hKN hk⟩, hk, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff (N := M.subgroupOf N) (⟨k, hKN hk⟩ : ↥N)).1 h1

end Group

section Module

variable {V : Type*} [CommGroup V] [Finite V]

theorem centralizer_fittingOf_le_fittingOf {G K A : Subgroup (MulAut V)}
    (hKG : K ≤ G) (hAG : A ≤ G) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3)
    (hFK : ⁅fittingOf G, K⁆ ≠ ⊥) (hG : G ≤ fittingOf G ⊔ (K ⊔ A)) :
    G ⊓ Subgroup.centralizer (fittingOf G : Set (MulAut V)) ≤ fittingOf G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := fittingOf G with hFdef
  have hFG : F ≤ G := fittingOf_le G
  have hFn : ∀ g ∈ G, ∀ f ∈ F, g * f * g⁻¹ ∈ F := fun g hg f hf => conj_mem_fittingOf hg hf
  have hFnil : Group.IsNilpotent ↥F := fittingOf_nilpotent G
  have hKnF : K ≤ Subgroup.normalizer (F : Set (MulAut V)) :=
    le_normalizer_of_conj fun k hk f hf => hFn k (hKG hk) f hf
  set N := F ⊔ K with hNdef
  have hNG : N ≤ G := sup_le hFG hKG
  have hAN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn =>
    conj_mem_sup_of_conj_mem hKnF (fun f hf => hFn a (hAG ha) f hf)
      (fun k hk => hAK a ha k hk) n hn
  have hAnormN : A ≤ Subgroup.normalizer (N : Set (MulAut V)) := le_normalizer_of_conj hAN
  have hGN : G ≤ N ⊔ A := by rw [hNdef, sup_assoc]; exact hG
  have hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨n', hn', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnormN).1 (hGN hg)
    have e : n' * a * n * (n' * a)⁻¹ = n' * (a * n * a⁻¹) * n'⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem hn' (hAN a ha n hn)) (N.inv_mem hn')
  set M := N ⊓ Subgroup.centralizer (F : Set (MulAut V)) with hMdef
  have hMN : M ≤ N := inf_le_left
  have hMG : M ≤ G := hMN.trans hNG
  have hMF : ∀ m ∈ M, ∀ f ∈ F, m * f = f * m := fun m hm f hf =>
    (Subgroup.mem_centralizer_iff.1 hm.2 f hf).symm
  have hcentn : ∀ {X : Subgroup (MulAut V)}, (∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) →
      ∀ g ∈ G, ∀ m ∈ X ⊓ Subgroup.centralizer (F : Set (MulAut V)),
        g * m * g⁻¹ ∈ X ⊓ Subgroup.centralizer (F : Set (MulAut V)) := by
    intro X hX g hg m hm
    refine ⟨hX g hg m hm.1, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
    have hf' : g⁻¹ * f * g ∈ F := by simpa using hFn g⁻¹ (G.inv_mem hg) f hf
    have h1 : m * (g⁻¹ * f * g) = (g⁻¹ * f * g) * m :=
      (Subgroup.mem_centralizer_iff.1 hm.2 _ hf').symm
    calc f * (g * m * g⁻¹) = g * ((g⁻¹ * f * g) * m) * g⁻¹ := by group
      _ = g * (m * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = (g * m * g⁻¹) * f := by group
  have hMn : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M := hcentn hNn
  have hdec : ∀ x ∈ M, ∃ f ∈ F, ∃ k ∈ K, x = f * k ∧ ∀ k' ∈ K, k * k' = k' * k := by
    rcases hK with hq | h3
    · have hMnF : M ≤ Subgroup.normalizer (F : Set (MulAut V)) :=
        le_normalizer_of_conj fun m hm f hf => by
          rw [show m * f * m⁻¹ = f from by rw [hMF m hm f hf]; group]
          exact hf
      have hXn : ∀ k ∈ K, ∀ x ∈ F ⊔ M, k * x * k⁻¹ ∈ F ⊔ M := fun k hk =>
        conj_mem_sup_of_conj_mem hMnF (fun f hf => hFn k (hKG hk) f hf)
          (fun m hm => hMn k (hKG hk) m hm)
      have hKX : ¬ K ≤ F ⊔ M := by
        intro hle
        have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
        have hKM : K ≤ M := perfect_le_of_nilpotent_quotient le_sup_left hMN
          (fun n hn m hm => hMn n (hNG hn) m hm) le_sup_right hle hperf
        apply hFK
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun k hk => (hKM hk).2
      have hnormX : ((K ⊓ (F ⊔ M)).subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun y k hy hk =>
          ⟨K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk), hXn k hk y hy.2⟩
      have hproper : (K ⊓ (F ⊔ M)).subgroupOf K ≠ ⊤ := by
        intro h
        apply hKX
        intro y hy
        have : (⟨y, hy⟩ : ↥K) ∈ (K ⊓ (F ⊔ M)).subgroupOf K := by rw [h]; trivial
        exact this.2
      have hcen := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq _ hproper
      intro x hx
      obtain ⟨f, hf, k, hk, hxfk⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hKnF).1 hx.1
      refine ⟨f, hf, k, hk, hxfk, fun k' hk' => ?_⟩
      have hkX : k ∈ F ⊔ M := by
        have e : k = f⁻¹ * x := by rw [hxfk]; group
        rw [e]
        exact Subgroup.mul_mem_sup (F.inv_mem hf) hx
      have hmem : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ (F ⊔ M)).subgroupOf K := ⟨hk, hkX⟩
      have := Subgroup.mem_center_iff.mp (hcen hmem) ⟨k', hk'⟩
      exact (congrArg Subtype.val this).symm
    · intro x hx
      obtain ⟨f, hf, k, hk, hxfk⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hKnF).1 hx.1
      refine ⟨f, hf, k, hk, hxfk, fun k' hk' => ?_⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥K := isCyclic_of_prime_card h3
      have hcomm : IsMulCommutative ↥K := inferInstance
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨k, hk⟩ ⟨k', hk'⟩)
  have hMcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ F := by
    intro x hx y hy
    obtain ⟨f, hf, k, hk, hxfk, hkc⟩ := hdec x hx
    obtain ⟨f', hf', k', hk', hyfk, -⟩ := hdec y hy
    rw [hxfk, hyfk]
    exact commutator_mem_of_commute_mod hf hf' (fun g hg => hFn k (hKG hk) g hg)
      (fun g hg => hFn k' (hKG hk') g hg) (hkc k' hk')
  have hcc : commutator ↥M ≤ Subgroup.center ↥M := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact hMF z z.2 _ (hMcomm x x.2 y y.2)
  have hMnil : Group.IsNilpotent ↥M := by
    apply Subgroup.isNilpotent_of_ker_le_center (Abelianization.of (G := ↥M))
    rwa [Abelianization.ker_of]
  have hMleF : M ≤ F := le_fittingOf_of_nilpotent_normal hMG hMn
  set D := G ⊓ Subgroup.centralizer (F : Set (MulAut V)) with hDdef
  have hDG : D ≤ G := inf_le_left
  have hDn : ∀ g ∈ G, ∀ d ∈ D, g * d * g⁻¹ ∈ D := hcentn (fun g hg x hx => G.mul_mem
    (G.mul_mem hg hx) (G.inv_mem hg))
  have hMD : M ≤ D := fun m hm => ⟨hMG hm, hm.2⟩
  have hDsq : ∀ d ∈ D, d ^ 2 ∈ M := by
    intro d hd
    exact ⟨sq_mem_of_mem_sup hAnormN hA2 d (hGN hd.1), (Subgroup.centralizer _).pow_mem hd.2 2⟩
  have hMcenter : M.subgroupOf D ≤ Subgroup.center ↥D := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 d.2.2 _ (hMleF hm)).symm
  have hMnormD : (M.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff hMD).2 fun m d hm hd => hMn d (hDG hd) m hm
  have hQ2 : IsPGroup 2 (↥D ⧸ M.subgroupOf D) := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hDsq d d.2
  have hQnil : Group.IsNilpotent (↥D ⧸ M.subgroupOf D) := hQ2.isNilpotent
  have hDnil : Group.IsNilpotent ↥D :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (M.subgroupOf D))
      (by rwa [QuotientGroup.ker_mk'])
  exact le_fittingOf_of_nilpotent_normal hDG hDn

end Module

end B1Red

end CFSG.Quasithin
