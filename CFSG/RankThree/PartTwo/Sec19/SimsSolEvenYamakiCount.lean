module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiPi3
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiOrb
public import CFSG.ClassicalInvolution.Solomon73

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open

@[expose] def conjSet {G : Type*} [Group G] (H : Subgroup G) (x : G) : Set G :=
  {y | ∃ h ∈ H, h * x * h⁻¹ = y}

theorem ncard_conjSet_mul {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    (conjSet H x).ncard * Nat.card (H ⊓ Subgroup.centralizer {x} : Subgroup G) = Nat.card H := by
  let _ : MulAction H G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (y : G), h • y = (h : G) * y * (h : G)⁻¹ := fun h y =>
    ConjAct.toConjAct_smul (h : G) y
  have horb : MulAction.orbit H x = conjSet H x := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h x).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul _ x⟩
  have hstab : MulAction.stabilizer H x = (Subgroup.centralizer {x}).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have h := (MulAction.stabilizer H x).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

theorem self_mem_conjSet {G : Type*} [Group G] (H : Subgroup G) (x : G) : x ∈ conjSet H x :=
  ⟨1, H.one_mem, by group⟩

theorem conj_mem_conjSet {G : Type*} [Group G] {H : Subgroup G} {x y : G} (hy : y ∈ conjSet H x)
    {k : G} (hk : k ∈ H) : k * y * k⁻¹ ∈ conjSet H x := by
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨k * h, H.mul_mem hk hh, by group⟩

theorem conjSet_mono {G : Type*} [Group G] {H H' : Subgroup G} (hHH : H ≤ H') (x : G) :
    conjSet H x ⊆ conjSet H' x := fun _ ⟨h, hh, hy⟩ => ⟨h, hHH hh, hy⟩

theorem isConj_of_mem_conjSet {G : Type*} [Group G] {H : Subgroup G} {x y : G}
    (hy : y ∈ conjSet H x) : IsConj x y := by
  obtain ⟨h, -, rfl⟩ := hy
  exact isConj_iff.mpr ⟨h, rfl⟩

theorem conjSet_normalizer_subset {G : Type*} [Group G] {A : Subgroup G} {x : G} (hx : x ∈ A) :
    conjSet (Subgroup.normalizer (A : Set G)) x ⊆ A := by
  rintro _ ⟨h, hh, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hh x).mp hx

theorem conjSet_finite {G : Type*} [Group G] [Finite G] (H : Subgroup G) (x : G) :
    (conjSet H x).Finite := Set.toFinite _

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

@[expose] noncomputable def σA (c : SC) : G := Y.ι ⟨cSp c, SW_le_Wsub (cSp_mem_SW c)⟩

theorem σA_mem_A (c : SC) : Y.σA c ∈ Y.A := Y.ι_mem_lift (cSp_mem_SW c)

theorem σA_mem_C (c : SC) : Y.σA c ∈ Subgroup.centralizer ({z} : Set G) := Y.ι_mem_C _

theorem ϑ_σA (c : SC) : (Y.ϑ ⟨Y.σA c, Y.σA_mem_C c⟩ : Wr 6) = cSp c :=
  congrArg Subtype.val (Y.ϑ_ι _)

theorem σA_add (c c' : SC) : Y.σA (c + c') = Y.σA c * Y.σA c' := by
  rw [σA, σA, σA, ← Y.ι_mul]
  congr 1
  exact Subtype.ext (cSp_add c c')

theorem σA_zero : Y.σA 0 = 1 := by
  rw [σA, show (⟨cSp 0, SW_le_Wsub (cSp_mem_SW 0)⟩ : ↥Wsub) = 1 from
    Subtype.ext cS_zero, map_one]

theorem σA_injective : Function.Injective Y.σA := by
  intro c c' h
  have h1 := Y.ι_injective h
  have h2 := cS_injective (congrArg Subtype.val h1)
  exact Prod.ext h2.1 h2.2

theorem exists_σA {a : G} (ha : a ∈ Y.A) : ∃ c, Y.σA c = a := by
  obtain ⟨haC, haS⟩ := Y.mem_lift.mp ha
  obtain ⟨c, hc⟩ := mem_SW_iff.mp haS
  refine ⟨c, ?_⟩
  apply Y.eq_of_ϑ_eq (hx := Y.σA_mem_C c) (hy := haC)
  rw [Y.ϑ_σA, ← hc]

theorem σA_one_zero : Y.σA (1, 0) = z := by
  refine Eq.trans ?_ Y.ι_allOnes
  rw [σA]
  congr 1

theorem σA_pi3 : Y.σA (sc [2]) = Y.π3 := by
  rw [σA, π3]
  congr 1
  exact Subtype.ext (by decide)

theorem σA_pi12 : Y.σA (sc [0, 1]) = Y.π12 := by
  rw [σA, π12]
  congr 1
  exact Subtype.ext (by decide)

@[expose] noncomputable def coord (X : Set G) : Finset SC :=
  haveI := Classical.decPred (fun c => Y.σA c ∈ X)
  Finset.univ.filter fun c => Y.σA c ∈ X

theorem mem_coord {X : Set G} {c : SC} : c ∈ Y.coord X ↔ Y.σA c ∈ X := by
  classical
  simp [coord]

theorem card_coord {X : Set G} (hX : X ⊆ Y.A) : (Y.coord X).card = X.ncard := by
  rw [← Set.ncard_coe_finset]
  have himg : Y.σA '' ↑(Y.coord X) = X := by
    ext a
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact Y.mem_coord.mp hc
    · intro ha
      obtain ⟨c, rfl⟩ := Y.exists_σA (hX ha)
      exact ⟨c, Y.mem_coord.mpr ha, rfl⟩
  conv_rhs => rw [← himg]
  rw [Set.ncard_image_of_injective _ Y.σA_injective]

end YData

theorem add_add_self_zmod2 : ∀ a b : ZMod 2, a + b + a = b := by decide

theorem conj_vec_gen (u w : Fin 6 → ZMod 2) (π : Perm (Fin 6)) :
    (⟨u, π⟩ : Wr 6) * ⟨w, 1⟩ * (⟨u, π⟩ : Wr 6)⁻¹ = ⟨pact π w, 1⟩ := by
  rw [mk_inv, mk_mul_mk, mk_mul_mk, mul_one, mul_inv_cancel]
  congr 1
  rw [← pact_mul, mul_inv_cancel, pact_one]
  funext i
  exact add_add_self_zmod2 _ _

theorem wMu_mem_Wsub : wMu ∈ Wsub := by show wsum wMu = 0; decide

theorem wMu'_mem_Wsub : wMu' ∈ Wsub := by show wsum wMu' = 0; decide

theorem wTau_mem_Wsub : wTau ∈ Wsub := by show wsum wTau = 0; decide

theorem wXi_mem_Wsub : wXi ∈ Wsub := by show wsum wXi = 0; decide

theorem actMu_actMu : ∀ x : SC, actMu (actMu x) = x := by decide

theorem actMu'_actMu' : ∀ x : SC, actMu' (actMu' x) = x := by decide

theorem actTau_actTau : ∀ x : SC, actTau (actTau x) = x := by decide

theorem actXi_actXi_actXi : ∀ x : SC, actXi (actXi (actXi x)) = x := by decide

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

theorem conj_σA_of {g : Wr 6} (hg : g ∈ Wsub) {f : SC → SC}
    (hf : ∀ x, g * cSp x * g⁻¹ = cSp (f x)) (c : SC) :
    Y.ι ⟨g, hg⟩ * Y.σA c * (Y.ι ⟨g, hg⟩)⁻¹ = Y.σA (f c) := by
  rw [σA, σA, ← map_inv, ← Y.ι_mul, ← Y.ι_mul]
  congr 1
  exact Subtype.ext (hf c)

theorem mem_normalizer_of {g : Wr 6} (hg : g ∈ Wsub) {f : SC → SC}
    (hf : ∀ x, g * cSp x * g⁻¹ = cSp (f x)) (hinv : ∀ x, ∃ y, f y = x) :
    Y.ι ⟨g, hg⟩ ∈ Subgroup.normalizer (Y.A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    obtain ⟨c, rfl⟩ := Y.exists_σA ha
    rw [Y.conj_σA_of hg hf]
    exact Y.σA_mem_A _
  · intro ha
    obtain ⟨c, hc⟩ := Y.exists_σA ha
    obtain ⟨y, rfl⟩ := hinv c
    rw [← Y.conj_σA_of hg hf] at hc
    have h1 : a = Y.σA y := by
      have h2 := congrArg (fun t => (Y.ι ⟨g, hg⟩)⁻¹ * t * Y.ι ⟨g, hg⟩) hc
      rw [show (Y.ι ⟨g, hg⟩)⁻¹ * (Y.ι ⟨g, hg⟩ * Y.σA y * (Y.ι ⟨g, hg⟩)⁻¹) * Y.ι ⟨g, hg⟩ =
        Y.σA y by group, show (Y.ι ⟨g, hg⟩)⁻¹ * (Y.ι ⟨g, hg⟩ * a * (Y.ι ⟨g, hg⟩)⁻¹) *
        Y.ι ⟨g, hg⟩ = a by group] at h2
      exact h2.symm
    rw [h1]
    exact Y.σA_mem_A y

theorem gens_mem_normalizer :
    Y.ι ⟨wMu, wMu_mem_Wsub⟩ ∈ Subgroup.normalizer (Y.A : Set G) ∧
    Y.ι ⟨wMu', wMu'_mem_Wsub⟩ ∈ Subgroup.normalizer (Y.A : Set G) ∧
    Y.ι ⟨wTau, wTau_mem_Wsub⟩ ∈ Subgroup.normalizer (Y.A : Set G) ∧
    Y.ι ⟨wXi, wXi_mem_Wsub⟩ ∈ Subgroup.normalizer (Y.A : Set G) :=
  ⟨Y.mem_normalizer_of _ conj_cS_wMu fun x => ⟨actMu x, actMu_actMu x⟩,
    Y.mem_normalizer_of _ conj_cS_wMu' fun x => ⟨actMu' x, actMu'_actMu' x⟩,
    Y.mem_normalizer_of _ conj_cS_wTau fun x => ⟨actTau x, actTau_actTau x⟩,
    Y.mem_normalizer_of _ conj_cS_wXi fun x => ⟨actXi (actXi x), actXi_actXi_actXi x⟩⟩

theorem coord_closed {X : Set G}
    (hX : ∀ x ∈ X, ∀ n ∈ Subgroup.normalizer (Y.A : Set G), n * x * n⁻¹ ∈ X) :
    IsClosedSC ↑(Y.coord X) := by
  intro c hc
  have hc' := Y.mem_coord.mp hc
  obtain ⟨h0, h1, h2, h3⟩ := Y.gens_mem_normalizer
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_coe, Y.mem_coord, ← Y.conj_σA_of wMu_mem_Wsub conj_cS_wMu]
    exact hX _ hc' _ h0
  · rw [Finset.mem_coe, Y.mem_coord, ← Y.conj_σA_of wMu'_mem_Wsub conj_cS_wMu']
    exact hX _ hc' _ h1
  · rw [Finset.mem_coe, Y.mem_coord, ← Y.conj_σA_of wTau_mem_Wsub conj_cS_wTau]
    exact hX _ hc' _ h2
  · rw [Finset.mem_coe, Y.mem_coord, ← Y.conj_σA_of wXi_mem_Wsub conj_cS_wXi]
    exact hX _ hc' _ h3

end YData

open CFSG.ClassicalInvolution.Solomon73 in
theorem isE64_map_conj {G : Type} [Group G] {B : Subgroup G} (hB : IsE64 B) (g : G) :
    IsE64 (B.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hc, hs, hcard⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hc x hx y hy]
    group
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hs x hx]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

open CFSG.ClassicalInvolution.Solomon73 in
theorem isE64_A : IsE64 Y.A := by
  refine ⟨fun a ha b hb => Y.A_comm ha hb, fun a ha => ?_, Y.card_A⟩
  obtain ⟨c, rfl⟩ := Y.exists_σA ha
  rw [← Y.σA_add, SC_add_self, Y.σA_zero]

open CFSG.ClassicalInvolution.Solomon73 in
theorem exists_normalizer_conj (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    {a b g : G} (ha : a ∈ Y.A) (hb : b ∈ Y.A) (hg : g * a * g⁻¹ = b) :
    ∃ n ∈ Subgroup.normalizer (Y.A : Set G), n * a * n⁻¹ = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  have hAp : IsPGroup 2 Y.A := IsPGroup.of_card (n := 6) (by rw [Y.card_A]; norm_num)
  set Ag := Y.A.map (MulAut.conj g).toMonoidHom with hAg
  have hAgp : IsPGroup 2 Ag := hAp.map _
  have hACb : Y.A ≤ Cb := fun x hx => by
    rw [hCb, Subgroup.mem_centralizer_singleton_iff]
    exact Y.A_comm hx hb
  have hAgCb : Ag ≤ Cb := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hCb, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    rw [show g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ by group, Y.A_comm ha hx]
    group
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := Cb)).exists_le_sylow
  obtain ⟨Q2, hQ2⟩ := (hAgp.comap_subtype (K := Cb)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥Cb) Q2 Q
  obtain ⟨P1, hP1⟩ := (Q.isPGroup'.map Cb.subtype).exists_le_sylow
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq G P P1
  have hmemP1 : ∀ x, x ∈ (P1 : Subgroup G) → t⁻¹ * x * t ∈ Y.T := by
    intro x hx
    rw [← ht, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [← hP]
    simpa [MulAut.inv_apply, MulAut.conj_symm_apply] using hx
  have hA_P1 : ∀ x ∈ Y.A, x ∈ (P1 : Subgroup G) := fun x hx =>
    hP1 ⟨⟨x, hACb hx⟩, hQ hx, rfl⟩
  have hcAg_P1 : ∀ x ∈ Y.A, (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ ∈ (P1 : Subgroup G) := by
    intro x hx
    have hxQ2 : (⟨g * x * g⁻¹, hAgCb ⟨x, hx, rfl⟩⟩ : ↥Cb) ∈ (Q2 : Subgroup ↥Cb) :=
      hQ2 ⟨x, hx, rfl⟩
    have hxQ : c * ⟨g * x * g⁻¹, hAgCb ⟨x, hx, rfl⟩⟩ * c⁻¹ ∈ (Q : Subgroup ↥Cb) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hxQ2
    exact hP1 ⟨_, hxQ, rfl⟩
  have h1 : Y.A.map (MulAut.conj t⁻¹).toMonoidHom = Y.A := by
    refine hE _ ?_ (isE64_map_conj Y.isE64_A _)
    rintro _ ⟨x, hx, rfl⟩
    have := hmemP1 x (hA_P1 x hx)
    simpa [MulAut.conj_apply] using this
  have h2 : Y.A.map (MulAut.conj (t⁻¹ * c * g)).toMonoidHom = Y.A := by
    refine hE _ ?_ (isE64_map_conj Y.isE64_A _)
    rintro _ ⟨x, hx, rfl⟩
    have := hmemP1 _ (hcAg_P1 x hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert this using 1
    group
  have hmap : ∀ k : G, Y.A.map (MulAut.conj k).toMonoidHom = Y.A →
      ∀ x, x ∈ Y.A ↔ k * x * k⁻¹ ∈ Y.A := by
    intro k hk x
    constructor
    · intro hx
      rw [← hk]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hk] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := by
        have := congrArg (fun s => k⁻¹ * s * k) hyx
        rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group,
          show k⁻¹ * (k * x * k⁻¹) * k = x by group] at this
      rw [← this]
      exact hy
  have hA1 := hmap _ h1
  have hA2 := hmap _ h2
  refine ⟨(c : G) * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hA2 x, hA1 ((c : G) * g * x * ((c : G) * g)⁻¹)]
    constructor <;> intro h <;> convert h using 1 <;> group
  · have hcb : (c : G) * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    calc (c : G) * g * a * ((c : G) * g)⁻¹ = c * (g * a * g⁻¹) * (c : G)⁻¹ := by group
      _ = c * b * (c : G)⁻¹ := by rw [hg]
      _ = b := by rw [hcb]; group

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
