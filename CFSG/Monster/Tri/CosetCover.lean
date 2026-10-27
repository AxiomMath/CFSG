module

public import CFSG.Monster.Schur.Defs
public import CFSG.Monster.Tri.TwoAShort
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.YGroups CFSG.Monster.B.Recog CFSG.Monster.GMS

section Coxeter

variable {M : Type*} [Group M] {x c y : M}

theorem coxeter_sq (hx : x * x = 1) (hc : c * c = 1) (hy : y * y = 1) (hcy : c * y = y * c) :
    x * c * y * x * (x * c * y * x) = 1 := by
  have h1 : c * y * (c * y) = 1 := by
    calc c * y * (c * y) = c * (y * c) * y := by simp only [mul_assoc]
      _ = c * (c * y) * y := by rw [hcy]
      _ = (c * c) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hc, hy, one_mul]
  have hx' : ∀ a, x * (x * a) = a := fun a => by rw [← mul_assoc, hx, one_mul]
  calc x * c * y * x * (x * c * y * x) = x * (c * y * (c * y)) * x := by
        simp only [mul_assoc]
        rw [hx']
    _ = 1 := by rw [h1, mul_one, hx]

theorem coxeter_conj (hx : x * x = 1) (hc : c * c = 1) (hy : y * y = 1) (hcy : c * y = y * c)
    (hcx : (c * x) ^ 3 = 1) (hxy : (x * y) ^ 3 = 1) :
    x * c * y * x * c * (x * c * y * x) = y := by
  have hc' : ∀ a, c * (c * a) = a := fun a => by rw [← mul_assoc, hc, one_mul]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxcx : x * c * x = c * x * c := by
    have h : c * x * c * (x * c * x) = 1 := by
      have := hcx
      rw [pow_succ, pow_succ, pow_one] at this
      simpa only [mul_assoc] using this
    have h2 := eq_inv_of_mul_eq_one_left h
    rw [mul_inv_rev, mul_inv_rev, hxi, hci] at h2
    simpa [mul_assoc] using h2.symm
  have hbraid : ∀ a, x * (c * (x * a)) = c * (x * (c * a)) := fun a => by
    simpa only [mul_assoc] using congrArg (· * a) hxcx
  have hcyc : ∀ a, c * (y * (c * a)) = y * a := fun a => by
    have : c * y * c = y := by rw [hcy, mul_assoc, hc, mul_one]
    calc c * (y * (c * a)) = (c * y * c) * a := by simp only [mul_assoc]
      _ = y * a := by rw [this]
  have hy3 : x * (y * (x * (y * x))) = y := by
    have h : x * y * x * y * x * y = 1 := by
      have := hxy
      rw [pow_succ, pow_succ, pow_one] at this
      simpa only [mul_assoc] using this
    have h2 := eq_inv_of_mul_eq_one_left h
    rw [hyi] at h2
    simpa only [mul_assoc] using h2
  simp only [mul_assoc]
  rw [hbraid, hc', hcyc, hy3]

end Coxeter

section CosetGraphLemmas

variable {Z : Type*} [Group Z] {K : Subgroup Z} {s : Z}

theorem cosetGraph_adj_mk_mk_iff (hs : s ∉ K) (hs₂ : s * s ∈ K) {z z' : Z} :
    (cosetGraph K s).Adj (z : Z ⧸ K) (z' : Z ⧸ K) ↔ ∃ a ∈ K, ∃ k ∈ K, z⁻¹ * z' = a * s * k := by
  rw [cosetGraph_adj_mk_iff hs hs₂]
  constructor
  · rintro ⟨a, ha, h⟩
    have h1 : z'⁻¹ * (z * a * s) ∈ K := QuotientGroup.eq.1 h
    refine ⟨a, ha, (z'⁻¹ * (z * a * s))⁻¹, K.inv_mem h1, ?_⟩
    group
  · rintro ⟨a, ha, k, hk, h⟩
    refine ⟨a, ha, QuotientGroup.eq.2 ?_⟩
    have : z' = z * (a * s * k) := by rw [← h]; group
    rw [this]
    convert K.inv_mem hk using 1
    group

theorem cosetGraph_reachable_of_mem_closure (hs : s ∉ K) (hs₂ : s * s ∈ K) {z : Z}
    (hz : z ∈ Subgroup.closure ((K : Set Z) ∪ {s})) :
    (cosetGraph K s).Reachable ((1 : Z) : Z ⧸ K) (z : Z ⧸ K) := by
  have hone : ∀ x ∈ K, ((x : Z) : Z ⧸ K) = ((1 : Z) : Z ⧸ K) := fun x hx =>
    QuotientGroup.eq.2 (by simpa using K.inv_mem hx)
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rw [hone x hx]
    · rw [Set.mem_singleton_iff.1 hx]
      refine SimpleGraph.Adj.reachable ?_
      simpa using cosetGraph_adj_mk_mul hs hs₂ 1 (c := s) (by simp)
  | one => rfl
  | mul x y _ _ ihx ihy =>
    refine ihx.trans ?_
    simpa [cosetGraphSMul_apply, MulAction.Quotient.smul_mk] using
      ihy.map (cosetGraphSMul K s x)
  | inv x _ ih =>
    refine SimpleGraph.Reachable.symm ?_
    simpa [cosetGraphSMul_apply, MulAction.Quotient.smul_mk] using
      ih.map (cosetGraphSMul K s x⁻¹)

theorem cosetGraph_connected (hs : s ∉ K) (hs₂ : s * s ∈ K)
    (hgen : Subgroup.closure ((K : Set Z) ∪ {s}) = ⊤) : (cosetGraph K s).Connected := by
  have : Nonempty (Z ⧸ K) := ⟨((1 : Z) : Z ⧸ K)⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
  have hz := cosetGraph_reachable_of_mem_closure hs hs₂ (hgen ▸ Subgroup.mem_top z)
  have hw := cosetGraph_reachable_of_mem_closure hs hs₂ (hgen ▸ Subgroup.mem_top w)
  exact hz.symm.trans hw

end CosetGraphLemmas

section Cover

variable {M G : Type*} [Group M] [Group G] (f : M →* G) (H : Subgroup M) (c S : M)

theorem smul_baseVertex_eq_self {a g : G} (hg : g * a = a * g) :
    g • baseVertex a = baseVertex a :=
  (smul_eq_self_iff g (baseVertex a)).2 (Subgroup.mem_centralizer_singleton_iff.2 hg)

theorem smul_baseVertex_eq_self_of_comm (hc : ∀ h ∈ H, h * c = c * h) :
    ∀ h ∈ H, f h • baseVertex (f c) = baseVertex (f c) := fun h hh =>
  smul_baseVertex_eq_self (by rw [← map_mul, ← map_mul, hc h hh])

@[expose] noncomputable def chi (hc : ∀ h ∈ H, h * c = c * h)
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c))) :
    cosetGraph H S →g twoAGraph (f c) :=
  cosetHom (fun g _ _ h => twoAGraph_adj_smul g h) f H S (baseVertex (f c))
    (smul_baseVertex_eq_self_of_comm f H c hc) hs

theorem chi_mk (hc : ∀ h ∈ H, h * c = c * h)
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c))) (z : M) :
    chi f H c S hc hs (z : M ⧸ H) = f z • baseVertex (f c) := rfl

theorem chi_smul (hc : ∀ h ∈ H, h * c = c * h)
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c))) (z : M)
    (b : M ⧸ H) : chi f H c S hc hs (z • b) = f z • chi f H c S hc hs b := by
  induction b using QuotientGroup.induction_on with
  | _ w =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, chi_mk, chi_mk, map_mul, mul_smul]

variable {f H c S}

theorem not_mem_of_adj (hmap : H.map f = Subgroup.centralizer {f c})
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c))) : S ∉ H := by
  intro hS
  have h1 : f S ∈ Subgroup.centralizer {f c} := hmap ▸ Subgroup.mem_map_of_mem f hS
  have h2 : f S • baseVertex (f c) = baseVertex (f c) := (smul_eq_self_iff _ _).2 h1
  rw [h2] at hs
  exact hs.ne rfl

theorem isCovering_chi (hc : ∀ h ∈ H, h * c = c * h) (hS2 : S * S = 1)
    (hmap : H.map f = Subgroup.centralizer {f c})
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    (hloc : ∀ u : ConjVert (f c), (twoAGraph (f c)).Adj (baseVertex (f c)) u →
      ∃ g ∈ Subgroup.centralizer {f c}, g • (f S • baseVertex (f c)) = u)
    (hB : ∀ k ∈ H, f k • (f S • baseVertex (f c)) = f S • baseVertex (f c) → S * k * S ∈ H) :
    IsCovering (chi f H c S hc hs) := by
  have hS : S ∉ H := not_mem_of_adj hmap hs
  have hS2' : S * S ∈ H := hS2 ▸ H.one_mem
  have hSinv : S⁻¹ = S := inv_eq_of_mul_eq_one_right hS2
  refine IsCovering.of_existsUnique fun b y hby => ?_
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective b
  rw [chi_mk] at hby
  have hy : (twoAGraph (f c)).Adj (baseVertex (f c)) ((f z)⁻¹ • y) := by
    simpa using twoAGraph_adj_smul (f z)⁻¹ hby
  obtain ⟨g, hg, hgy⟩ := hloc _ hy
  obtain ⟨a, ha, rfl⟩ : g ∈ H.map f := hmap ▸ hg
  refine ⟨((z * a * S : M) : M ⧸ H), ⟨(cosetGraph_adj_mk_iff hS hS2').2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
  · rw [chi_mk, map_mul, map_mul, mul_smul, mul_smul, hgy, smul_inv_smul]
  · rintro b' ⟨hb', hb'y⟩
    obtain ⟨a', ha', rfl⟩ := (cosetGraph_adj_mk_iff hS hS2').1 hb'
    rw [chi_mk, map_mul, map_mul, mul_smul, mul_smul] at hb'y
    have h1 : f a' • (f S • baseVertex (f c)) = f a • (f S • baseVertex (f c)) := by
      rw [hgy, ← hb'y, inv_smul_smul]
    have hk : f (a'⁻¹ * a) • (f S • baseVertex (f c)) = f S • baseVertex (f c) := by
      rw [map_mul, map_inv, mul_smul, ← h1, inv_smul_smul]
    have hSk := hB _ (H.mul_mem (H.inv_mem ha') ha) hk
    rw [QuotientGroup.eq]
    convert hSk using 1
    simp [mul_assoc, hSinv]

theorem cosetGraph_connected_of_adj (hS2 : S * S = 1)
    (hmap : H.map f = Subgroup.centralizer {f c})
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    (hgen : Subgroup.closure ((H : Set M) ∪ {S}) = ⊤) : (cosetGraph H S).Connected :=
  cosetGraph_connected (not_mem_of_adj hmap hs) (hS2 ▸ H.one_mem) hgen

theorem ker_mk_injective (hinj : Set.InjOn f H) {k k' : M} (hk : k ∈ f.ker) (hk' : k' ∈ f.ker)
    (h : (k : M ⧸ H) = (k' : M ⧸ H)) : k = k' := by
  have h1 : k⁻¹ * k' ∈ H := QuotientGroup.eq.1 h
  have h2 : f (k⁻¹ * k') = f 1 := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, MonoidHom.mem_ker.1 hk']
    simp
  exact inv_mul_eq_one.1 (hinj h1 H.one_mem h2)

noncomputable def kerEquivFibre (hc : ∀ h ∈ H, h * c = c * h)
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    (hinj : Set.InjOn f H) (hmap : H.map f = Subgroup.centralizer {f c}) :
    f.ker ≃ {b : M ⧸ H // chi f H c S hc hs b = baseVertex (f c)} :=
  Equiv.ofBijective
    (fun n => ⟨(n.1 : M ⧸ H), by rw [chi_mk, MonoidHom.mem_ker.1 n.2, one_smul]⟩)
    ⟨fun n n' h => Subtype.ext (ker_mk_injective hinj n.2 n'.2 (congrArg Subtype.val h)),
      fun ⟨b, hb⟩ => by
        obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective b
        rw [chi_mk] at hb
        have hz : f z ∈ Subgroup.centralizer {f c} := (smul_eq_self_iff _ _).1 hb
        obtain ⟨h, hh, hfh⟩ : f z ∈ H.map f := hmap ▸ hz
        refine ⟨⟨z * h⁻¹, ?_⟩, Subtype.ext ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hfh, mul_inv_cancel]
        · show (((z * h⁻¹ : M) : M ⧸ H)) = (z : M ⧸ H)
          rw [QuotientGroup.eq]
          simpa using hh⟩

theorem exists_ker_eq_one_or_eq (hc : ∀ h ∈ H, h * c = c * h) (hinj : Set.InjOn f H)
    (hmap : H.map f = Subgroup.centralizer {f c}) (hS2 : S * S = 1)
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    (hloc : ∀ u : ConjVert (f c), (twoAGraph (f c)).Adj (baseVertex (f c)) u →
      ∃ g ∈ Subgroup.centralizer {f c}, g • (f S • baseVertex (f c)) = u)
    (hB : ∀ k ∈ H, f k • (f S • baseVertex (f c)) = f S • baseVertex (f c) → S * k * S ∈ H)
    (hgen : Subgroup.closure ((H : Set M) ∪ {S}) = ⊤)
    (hlift : LiftsMarked (chi f H c S hc hs) (longTri (f c)))
    (hinv : f c * f c = 1) (hne : f c ≠ 1) (htri : Triangulable (twoAGraph (f c)))
    (hΩ : ∀ x : ConjVert (f c),
      (longLinkGraph (twoAGraph (f c)) (longTri (f c)) x).Preconnected)
    (hq : ∀ {x y u : ConjVert (f c)} (hxy : (twoAGraph (f c)).Adj x y)
      (hxu : (twoAGraph (f c)).Adj x u) (hyu : (twoAGraph (f c)).Adj y u)
      (hL : permClosure (longTri (f c)) x y u),
      MarkedHomotopic (longTri (f c)) ((shortStruct_twoAGraph hinv hne).quad hxy hxu hyu hL)
        .nil) :
    ∃ n : M, ∀ k ∈ f.ker, k = 1 ∨ k = n := by
  have hcov := isCovering_chi hc hS2 hmap hs hloc hB
  have hconn := cosetGraph_connected_of_adj hS2 hmap hs hgen
  have ha : chi f H c S hc hs ((1 : M) : M ⧸ H) = baseVertex (f c) := by
    rw [chi_mk, map_one, one_smul]
  have key : ∀ k ∈ f.ker, k = 1 ∨ (k : M ⧸ H) =
      hcov.liftEnd ((shortStruct_twoAGraph hinv hne).loop hs) ((1 : M) : M ⧸ H) ha := by
    intro k hk
    have hb : chi f H c S hc hs (k : M ⧸ H) = baseVertex (f c) := by
      rw [chi_mk, MonoidHom.mem_ker.1 hk, one_smul]
    rcases card_fibre_le_two hcov hlift hconn.preconnected
      ((shortStruct_twoAGraph hinv hne).loop hs)
      (fun p => homotopy_class_le_two (shortStruct_twoAGraph hinv hne) htri hΩ hq hs p) ha hb
      with h | h
    · exact Or.inl (ker_mk_injective hinj hk (MonoidHom.mem_ker.2 (map_one f)) h)
    · exact Or.inr h
  by_cases hex : ∃ k ∈ f.ker, k ≠ 1
  · obtain ⟨n, hn, hn1⟩ := hex
    refine ⟨n, fun k hk => ?_⟩
    rcases key k hk with h | h
    · exact Or.inl h
    · rcases key n hn with h' | h'
      · exact absurd h' hn1
      · exact Or.inr (ker_mk_injective hinj hk hn (h.trans h'.symm))
  · exact ⟨1, fun k hk => Or.inl (by_contra fun h => hex ⟨k, hk, h⟩)⟩

theorem card_ker_le_two_of {n : M} (h : ∀ k ∈ f.ker, k = 1 ∨ k = n) :
    Finite f.ker ∧ Nat.card f.ker ≤ 2 := by
  have hsub : (f.ker : Set M) ⊆ {1, n} := fun k hk => by
    rcases h k hk with rfl | rfl <;> simp
  have hfin : (({1, n} : Set M)).Finite := Set.toFinite _
  refine ⟨(hfin.subset hsub).to_subtype, ?_⟩
  calc Nat.card f.ker = (f.ker : Set M).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, n} : Set M).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp

theorem finite_of_finite_ker {M G : Type*} [Group M] [Group G] (f : M →* G)
    (hf : Function.Surjective f) [Finite G] (hk : Finite f.ker) : Finite M := by
  have : Finite (M ⧸ f.ker) :=
    Finite.of_equiv G (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toEquiv
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := f.ker)).symm

theorem liftsMarked_chi_of_base (hc : ∀ h ∈ H, h * c = c * h)
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    (hbase : ∀ y z : ConjVert (f c), (twoAGraph (f c)).Adj (baseVertex (f c)) y →
      (twoAGraph (f c)).Adj y z → (twoAGraph (f c)).Adj z (baseVertex (f c)) →
      permClosure (longTri (f c)) (baseVertex (f c)) y z →
      ∃ b b' : M, (cosetGraph H S).Adj ((1 : M) : M ⧸ H) (b : M ⧸ H) ∧
        (cosetGraph H S).Adj (b : M ⧸ H) (b' : M ⧸ H) ∧
        (cosetGraph H S).Adj (b' : M ⧸ H) ((1 : M) : M ⧸ H) ∧
        f b • baseVertex (f c) = y ∧ f b' • baseVertex (f c) = z) :
    LiftsMarked (chi f H c S hc hs) (longTri (f c)) := by
  intro b y z h1 h2 h3 hT
  obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective b
  rw [chi_mk] at h1 h3 hT
  have h1' : (twoAGraph (f c)).Adj (baseVertex (f c)) ((f z₀)⁻¹ • y) := by
    simpa using twoAGraph_adj_smul (f z₀)⁻¹ h1
  have h2' : (twoAGraph (f c)).Adj ((f z₀)⁻¹ • y) ((f z₀)⁻¹ • z) := twoAGraph_adj_smul _ h2
  have h3' : (twoAGraph (f c)).Adj ((f z₀)⁻¹ • z) (baseVertex (f c)) := by
    simpa using twoAGraph_adj_smul (f z₀)⁻¹ h3
  have hT' : permClosure (longTri (f c)) (baseVertex (f c)) ((f z₀)⁻¹ • y) ((f z₀)⁻¹ • z) := by
    have := (equivariantShort_twoAGraph (a := f c)).permClosure_smul (f z₀)⁻¹ hT
    simpa using this
  obtain ⟨b, b', hb1, hb2, hb3, hy, hz⟩ := hbase _ _ h1' h2' h3' hT'
  have hmul : ∀ w : M, (z₀ : M) • ((w : M) : M ⧸ H) = ((z₀ * w : M) : M ⧸ H) := fun w => rfl
  refine ⟨((z₀ * b : M) : M ⧸ H), ((z₀ * b' : M) : M ⧸ H), ?_, ?_, ?_, ?_, ?_⟩
  · have := cosetGraph_adj_smul z₀ hb1
    rwa [hmul, hmul, mul_one] at this
  · have := cosetGraph_adj_smul z₀ hb2
    rwa [hmul, hmul] at this
  · have := cosetGraph_adj_smul z₀ hb3
    rwa [hmul, hmul, mul_one] at this
  · rw [chi_mk, map_mul, mul_smul, hy, smul_inv_smul]
  · rw [chi_mk, map_mul, mul_smul, hz, smul_inv_smul]

section Lift

variable (H' : Subgroup M)

theorem mk_eq_of_smul_eq_of_mem (hinj' : Set.InjOn f H')
    (hRH : H.map f ⊓ H'.map f ≤ (H ⊓ H').map f)
    (hmap : H.map f = Subgroup.centralizer {f c}) {h h' : M} (hh : h ∈ H') (hh' : h' ∈ H')
    (he : f h • baseVertex (f c) = f h' • baseVertex (f c)) : (h : M ⧸ H) = (h' : M ⧸ H) := by
  have hm : h'⁻¹ * h ∈ H' := H'.mul_mem (H'.inv_mem hh') hh
  have h1 : f (h'⁻¹ * h) • baseVertex (f c) = baseVertex (f c) := by
    rw [map_mul, map_inv, mul_smul, he, inv_smul_smul]
  have h2 : f (h'⁻¹ * h) ∈ H.map f := hmap ▸ (smul_eq_self_iff _ _).1 h1
  obtain ⟨r, hr, hrf⟩ := hRH ⟨h2, Subgroup.mem_map_of_mem f hm⟩
  have hrh : r = h'⁻¹ * h := hinj' hr.2 hm hrf
  rw [QuotientGroup.eq]
  have := H.inv_mem hr.1
  rwa [hrh, mul_inv_rev, inv_inv] at this

theorem exists_lift_of_orbit_triangle (hS2 : S * S = 1) (hS' : S ∈ H') (hinj' : Set.InjOn f H')
    (hRH : H.map f ⊓ H'.map f ≤ (H ⊓ H').map f)
    (hmap : H.map f = Subgroup.centralizer {f c})
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    {β γ : ConjVert (f c)}
    (h₁ : ∃ h ∈ H', f h • baseVertex (f c) = baseVertex (f c) ∧
      f h • (f S • baseVertex (f c)) = β)
    (h₂ : ∃ h ∈ H', f h • baseVertex (f c) = baseVertex (f c) ∧
      f h • (f S • baseVertex (f c)) = γ)
    (h₃ : ∃ h ∈ H', f h • baseVertex (f c) = β ∧ f h • (f S • baseVertex (f c)) = γ) :
    ∃ b b' : M, (cosetGraph H S).Adj ((1 : M) : M ⧸ H) (b : M ⧸ H) ∧
      (cosetGraph H S).Adj (b : M ⧸ H) (b' : M ⧸ H) ∧
      (cosetGraph H S).Adj (b' : M ⧸ H) ((1 : M) : M ⧸ H) ∧
      f b • baseVertex (f c) = β ∧ f b' • baseVertex (f c) = γ := by
  have hS : S ∉ H := not_mem_of_adj hmap hs
  have hS2' : S * S ∈ H := hS2 ▸ H.one_mem
  obtain ⟨a₁, ha₁, hv₁, hw₁⟩ := h₁
  obtain ⟨a₂, ha₂, hv₂, hw₂⟩ := h₂
  obtain ⟨a₃, ha₃, hv₃, hw₃⟩ := h₃
  have hmem : ∀ {a : M}, a ∈ H' → f a • baseVertex (f c) = baseVertex (f c) → a ∈ H :=
    fun {a} ha hv => by
      have := mk_eq_of_smul_eq_of_mem H' hinj' hRH hmap ha H'.one_mem
        (by rw [map_one, one_smul]; exact hv)
      simpa using H.inv_mem (QuotientGroup.eq.1 this)
  have ha₁H : a₁ ∈ H := hmem ha₁ hv₁
  have ha₂H : a₂ ∈ H := hmem ha₂ hv₂
  have e₁ : ((a₁ * S : M) : M ⧸ H) = (a₃ : M ⧸ H) :=
    mk_eq_of_smul_eq_of_mem H' hinj' hRH hmap (H'.mul_mem ha₁ hS') ha₃
      (by rw [map_mul, mul_smul, hw₁, hv₃])
  have e₂ : ((a₂ * S : M) : M ⧸ H) = ((a₃ * S : M) : M ⧸ H) :=
    mk_eq_of_smul_eq_of_mem H' hinj' hRH hmap (H'.mul_mem ha₂ hS') (H'.mul_mem ha₃ hS')
      (by rw [map_mul, mul_smul, hw₂, map_mul, mul_smul, hw₃])
  have hadj₁ : (cosetGraph H S).Adj ((1 : M) : M ⧸ H) ((a₁ * S : M) : M ⧸ H) :=
    (cosetGraph_adj_mk_iff hS hS2').2 ⟨a₁, ha₁H, by rw [one_mul]⟩
  have hadj₂ : (cosetGraph H S).Adj ((1 : M) : M ⧸ H) ((a₂ * S : M) : M ⧸ H) :=
    (cosetGraph_adj_mk_iff hS hS2').2 ⟨a₂, ha₂H, by rw [one_mul]⟩
  refine ⟨a₁ * S, a₂ * S, hadj₁, ?_, hadj₂.symm, ?_, ?_⟩
  · rw [e₁, e₂]
    exact cosetGraph_adj_mk_mul hS hS2' a₃ (by rw [inv_mul_cancel]; exact H.one_mem)
  · rw [map_mul, mul_smul, hw₁]
  · rw [map_mul, mul_smul, hw₂]

variable {H'}

theorem exists_lift_of_trans (hS2 : S * S = 1) (hS' : S ∈ H') (hinj' : Set.InjOn f H')
    (hRH : H.map f ⊓ H'.map f ≤ (H ⊓ H').map f)
    (hmap : H.map f = Subgroup.centralizer {f c})
    (hs : (twoAGraph (f c)).Adj (baseVertex (f c)) (f S • baseVertex (f c)))
    (htrans : ∀ y z y' z' : ConjVert (f c), longTri (f c) (baseVertex (f c)) y z →
      longTri (f c) (baseVertex (f c)) y' z' →
      ∃ g ∈ Subgroup.centralizer {f c}, g • y = y' ∧ g • z = z')
    (hV : ∃ β γ : ConjVert (f c), longTri (f c) (baseVertex (f c)) β γ ∧
      (∃ h ∈ H', f h • baseVertex (f c) = baseVertex (f c) ∧
        f h • (f S • baseVertex (f c)) = β) ∧
      (∃ h ∈ H', f h • baseVertex (f c) = baseVertex (f c) ∧
        f h • (f S • baseVertex (f c)) = γ) ∧
      (∃ h ∈ H', f h • baseVertex (f c) = β ∧ f h • (f S • baseVertex (f c)) = γ))
    (y z : ConjVert (f c)) (hyz : longTri (f c) (baseVertex (f c)) y z) :
    ∃ b b' : M, (cosetGraph H S).Adj ((1 : M) : M ⧸ H) (b : M ⧸ H) ∧
      (cosetGraph H S).Adj (b : M ⧸ H) (b' : M ⧸ H) ∧
      (cosetGraph H S).Adj (b' : M ⧸ H) ((1 : M) : M ⧸ H) ∧
      f b • baseVertex (f c) = y ∧ f b' • baseVertex (f c) = z := by
  have hS : S ∉ H := not_mem_of_adj hmap hs
  have hS2' : S * S ∈ H := hS2 ▸ H.one_mem
  obtain ⟨β, γ, hβγ, h₁, h₂, h₃⟩ := hV
  obtain ⟨b₁, b₂, hb1, hb12, hb2, hbβ, hbγ⟩ :=
    exists_lift_of_orbit_triangle H' hS2 hS' hinj' hRH hmap hs h₁ h₂ h₃
  obtain ⟨g, hg, hgβ, hgγ⟩ := htrans _ _ _ _ hβγ hyz
  obtain ⟨a, ha, rfl⟩ : g ∈ H.map f := hmap ▸ hg
  have hmul : ∀ w : M, a • ((w : M) : M ⧸ H) = ((a * w : M) : M ⧸ H) := fun w => rfl
  have ha1 : ((a * 1 : M) : M ⧸ H) = ((1 : M) : M ⧸ H) := by
    rw [mul_one, QuotientGroup.eq]
    simpa using H.inv_mem ha
  refine ⟨a * b₁, a * b₂, ?_, ?_, ?_, ?_, ?_⟩
  · have := cosetGraph_adj_smul a hb1
    rwa [hmul, hmul, ha1] at this
  · have := cosetGraph_adj_smul a hb12
    rwa [hmul, hmul] at this
  · have := cosetGraph_adj_smul a hb2
    rwa [hmul, hmul, ha1] at this
  · rw [map_mul, mul_smul, hbβ, hgβ]
  · rw [map_mul, mul_smul, hbγ, hgγ]

end Lift

end Cover

theorem ker_eq_bot_of_noPerfectDoubleCover {M : Type} {G : Type*} [Group G] [Group M]
    (f : M →* G) (hsurj : Function.Surjective f) (hperf : Group.IsPerfect M)
    (hND : CFSG.Monster.Schur.NoPerfectDoubleCover G) {n : M}
    (h : ∀ k ∈ f.ker, k = 1 ∨ k = n) : f.ker = ⊥ := by
  by_contra hne
  obtain ⟨k₀, hk₀, hk₀1⟩ : ∃ k ∈ f.ker, k ≠ 1 := by
    by_contra hcon
    exact hne ((Subgroup.eq_bot_iff_forall _).2 fun k hk =>
      by_contra fun h => hcon ⟨k, hk, h⟩)
  refine hND M f hsurj hperf ?_
  rw [Nat.card_eq_two_iff]
  have hk₀n : k₀ = n := (h k₀ hk₀).resolve_left hk₀1
  refine ⟨⟨1, f.ker.one_mem⟩, ⟨k₀, hk₀⟩, fun e => hk₀1 (congrArg Subtype.val e).symm, ?_⟩
  ext ⟨k, hk⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true,
    Subtype.mk.injEq]
  rcases h k hk with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h1.trans hk₀n.symm)

end CFSG.Monster.Tri
