module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

namespace GE23

section Comp

variable {V : Type} [CommGroup V] {I : Finset (Subgroup (MulAut V))}

theorem mem_fixV_zpowers_iff' {g : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem exists_restr
    (hother : ∀ H ∈ I, ∀ H' ∈ I, H' ≠ H → ∀ y ∈ H', ∀ u ∈ commV H, y u = u)
    (hstab : ∀ H ∈ I, ∀ y ∈ H, ∀ u ∈ commV H, y u ∈ commV H)
    {A : Subgroup (MulAut V) → Subgroup (MulAut V)} (hA : ∀ H ∈ I, A H ≤ H)
    {y : MulAut V} (hy : y ∈ ⨆ H ∈ I, A H) {H : Subgroup (MulAut V)} (hH : H ∈ I) :
    ∃ a ∈ A H, ∀ u ∈ commV H, y u = a u := by
  classical
  let K : Subgroup (MulAut V) :=
    { carrier := {y | ∃ a ∈ A H, ∀ u ∈ commV H, y u = a u}
      one_mem' := ⟨1, Subgroup.one_mem _, fun u _ => rfl⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, Subgroup.mul_mem _ ha₁ ha₂, fun u hu => ?_⟩
        show y₁ (y₂ u) = a₁ (a₂ u)
        rw [h₂ u hu]
        exact h₁ _ (hstab H hH a₂ (hA H hH ha₂) u hu)
      inv_mem' := by
        rintro y ⟨a, ha, h⟩
        refine ⟨a⁻¹, Subgroup.inv_mem _ ha, fun u hu => ?_⟩
        have hu' : a⁻¹ u ∈ commV H := hstab H hH a⁻¹ (Subgroup.inv_mem _ (hA H hH ha)) u hu
        have h3 : y (a⁻¹ u) = u := by
          rw [h (a⁻¹ u) hu']
          show a (a⁻¹ u) = u
          simp
        show y⁻¹ u = a⁻¹ u
        calc y⁻¹ u = y⁻¹ (y (a⁻¹ u)) := by rw [h3]
          _ = a⁻¹ u := by simp }
  have hle : (⨆ H' ∈ I, A H') ≤ K := by
    refine iSup₂_le fun H' hH' z hz => ?_
    by_cases hHH : H' = H
    · subst hHH
      exact ⟨z, hz, fun u _ => rfl⟩
    · exact ⟨1, Subgroup.one_mem _, fun u hu => by
        rw [hother H hH H' hH' hHH z (hA H' hH' hz) u hu]
        rfl⟩
  exact hle hy

theorem mem_iSup_of_restr
    (hcomm : ∀ H ∈ I, ∀ H' ∈ I, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a)
    (hother : ∀ H ∈ I, ∀ H' ∈ I, H' ≠ H → ∀ y ∈ H', ∀ u ∈ commV H, y u = u)
    (hstab : ∀ H ∈ I, ∀ y ∈ H, ∀ u ∈ commV H, y u ∈ commV H)
    (hsplit : ∀ v : V, ∃ w ∈ ⨆ H ∈ I, commV H, ∃ c ∈ fixV (⨆ H ∈ I, H), v = w * c)
    {A : Subgroup (MulAut V) → Subgroup (MulAut V)} (hA : ∀ H ∈ I, A H ≤ H)
    {y : MulAut V} (hy : y ∈ ⨆ H ∈ I, H)
    (h : ∀ H ∈ I, ∃ a ∈ A H, ∀ u ∈ commV H, y u = a u) : y ∈ ⨆ H ∈ I, A H := by
  classical
  have key : ∀ s : Finset (Subgroup (MulAut V)), s ⊆ I →
      ∃ e ∈ ⨆ H ∈ s, A H, ∀ H ∈ s, ∀ u ∈ commV H, (y * e⁻¹) u = u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨1, Subgroup.one_mem _, fun H hH => absurd hH (by simp)⟩
    | insert a s ha ih =>
      intro hs
      have haI : a ∈ I := hs (Finset.mem_insert_self a s)
      have hsI : s ⊆ I := fun x hx => hs (Finset.mem_insert_of_mem hx)
      obtain ⟨es, hes, hesT⟩ := ih hsI
      obtain ⟨aa, haa, haaU⟩ := h a haI
      have haaa : aa ∈ a := hA a haI haa
      have hes_triv : ∀ x ∈ ⨆ H ∈ s, A H, ∀ u ∈ commV a, x u = u := by
        intro x hx u hu
        have : (⨆ H ∈ s, A H) ≤ MulAction.stabilizer (MulAut V) u := by
          refine iSup₂_le fun H hH z hz => ?_
          rw [MulAction.mem_stabilizer_iff]
          exact hother a haI H (hsI hH) (fun e => ha (e ▸ hH)) z (hA H (hsI hH) hz) u hu
        exact MulAction.mem_stabilizer_iff.1 (this hx)
      have hcomm' : aa * es = es * aa := by
        have : (⨆ H ∈ s, A H) ≤ Subgroup.centralizer ({aa} : Set (MulAut V)) := by
          refine iSup₂_le fun H hH z hz => ?_
          refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact hcomm a haI H (hsI hH) (fun e => ha (e ▸ hH)) x haaa z (hA H (hsI hH) hz)
        exact Subgroup.mem_centralizer_iff.1 (this hes) aa rfl
      refine ⟨aa * es, ?_, ?_⟩
      · rw [Finset.iSup_insert]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haa) (Subgroup.mem_sup_right hes)
      · have hinv : (aa * es)⁻¹ = es⁻¹ * aa⁻¹ := mul_inv_rev aa es
        intro H hH u hu
        rcases Finset.mem_insert.1 hH with rfl | hHs
        ·
          have hu' : aa⁻¹ u ∈ commV H := hstab H haI aa⁻¹ (Subgroup.inv_mem _ haaa) u hu
          have h1 : es⁻¹ (aa⁻¹ u) = aa⁻¹ u := hes_triv _ (Subgroup.inv_mem _ hes) _ hu'
          show y ((aa * es)⁻¹ u) = u
          rw [hinv]
          show y (es⁻¹ (aa⁻¹ u)) = u
          rw [h1, haaU _ hu']
          simp
        · have h1 : aa⁻¹ u = u := by
            have := hother H (hsI hHs) a haI (fun e => ha (e ▸ hHs)) aa⁻¹
              (Subgroup.inv_mem _ haaa) u hu
            exact this
          show y ((aa * es)⁻¹ u) = u
          rw [hinv]
          show y (es⁻¹ (aa⁻¹ u)) = u
          rw [h1]
          exact hesT H hHs u hu
  obtain ⟨e, he, heT⟩ := key I subset_rfl
  have heY : e ∈ ⨆ H ∈ I, H := (iSup₂_mono fun H hH => hA H hH) he
  have hzY : y * e⁻¹ ∈ ⨆ H ∈ I, H := Subgroup.mul_mem _ hy (Subgroup.inv_mem _ heY)
  have hz1 : y * e⁻¹ = 1 := by
    ext v
    obtain ⟨w, hw, c, hc, rfl⟩ := hsplit v
    have hwfix : (⨆ H ∈ I, commV H) ≤ fixV (Subgroup.zpowers (y * e⁻¹)) :=
      iSup₂_le fun H hH x hx => (mem_fixV_zpowers_iff' (g := y * e⁻¹)).2 (heT H hH x hx)
    have h1 : (y * e⁻¹) w = w := (mem_fixV_zpowers_iff' (g := y * e⁻¹)).1 (hwfix hw)
    have h2 : (y * e⁻¹) c = c := hc _ hzY
    show (y * e⁻¹) (w * c) = w * c
    rw [map_mul, h1, h2]
  have : y = e := by
    have := congrArg (· * e) hz1
    simpa using this
  rw [this]
  exact he

theorem restr_mem_commV
    (hother : ∀ H ∈ I, ∀ H' ∈ I, H' ≠ H → ∀ y ∈ H', ∀ u ∈ commV H, y u = u)
    (hstab : ∀ H ∈ I, ∀ y ∈ H, ∀ u ∈ commV H, y u ∈ commV H)
    {b : MulAut V} (hb : b ∈ ⨆ H ∈ I, H) {H : Subgroup (MulAut V)} (hH : H ∈ I) {u : V}
    (hu : u ∈ commV H) : b u ∈ commV H := by
  obtain ⟨a, ha, h⟩ := exists_restr hother hstab (A := fun H => H) (fun _ _ => le_rfl) hb hH
  rw [h u hu]
  exact hstab H hH a ha u hu

theorem card_fixV_prod [Finite V]
    (hother : ∀ H ∈ I, ∀ H' ∈ I, H' ≠ H → ∀ y ∈ H', ∀ u ∈ commV H, y u = u)
    (hstab : ∀ H ∈ I, ∀ y ∈ H, ∀ u ∈ commV H, y u ∈ commV H)
    (hind0 : ∀ H ∈ I, commV H ⊓ (⨆ H' ∈ I, ⨆ (_ : H' ≠ H), commV H') = ⊥)
    (hsplit : ∀ v : V, ∃ w ∈ ⨆ H ∈ I, commV H, ∃ c ∈ fixV (⨆ H ∈ I, H), v = w * c)
    {B : Subgroup (MulAut V)} (hB : B ≤ ⨆ H ∈ I, H) :
    Nat.card V * ∏ H ∈ I, Nat.card ↥(commV H ⊓ fixV B) =
      Nat.card ↥(fixV B) * ∏ H ∈ I, Nat.card ↥(commV H) := by
  classical
  set F := fixV B with hF
  have hCF : fixV (⨆ H ∈ I, H) ≤ F := B1.fixV_le_fixV hB
  have key : ∀ s : Finset (Subgroup (MulAut V)), s ⊆ I →
      Nat.card ↥(F ⊔ ⨆ H ∈ s, commV H) * ∏ H ∈ s, Nat.card ↥(commV H ⊓ F) =
        Nat.card ↥F * ∏ H ∈ s, Nat.card ↥(commV H) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have h0 : (⨆ H ∈ (∅ : Finset (Subgroup (MulAut V))), commV H) = ⊥ := by simp
      rw [h0, sup_bot_eq, Finset.prod_empty, Finset.prod_empty, mul_one]
    | insert a s ha ih =>
      intro hs
      have haI : a ∈ I := hs (Finset.mem_insert_self a s)
      have hsI : s ⊆ I := fun x hx => hs (Finset.mem_insert_of_mem hx)
      have ih' := ih hsI
      set W := ⨆ H ∈ s, commV H with hW
      have hinf : (F ⊔ W) ⊓ commV a = commV a ⊓ F := by
        refine le_antisymm ?_ (le_inf (inf_le_right.trans (le_sup_of_le_left le_rfl)) inf_le_left)
        rintro x ⟨hx1, hx2⟩
        refine ⟨hx2, ?_⟩
        obtain ⟨f, hf, w, hw, rfl⟩ := Subgroup.mem_sup.1 hx1
        intro b hb
        have hbY : b ∈ ⨆ H ∈ I, H := hB hb
        have hbW : b w ∈ W := by
          have : W.map b.toMonoidHom ≤ W := by
            rw [hW, Subgroup.map_iSup]
            refine iSup_le fun H => ?_
            rw [Subgroup.map_iSup]
            refine iSup_le fun hH => ?_
            intro z hz
            obtain ⟨u, hu, rfl⟩ := hz
            exact le_iSup₂_of_le (f := fun H' (_ : H' ∈ s) => commV H') H hH le_rfl
              (restr_mem_commV hother hstab hbY (hsI hH) hu)
          exact this ⟨w, hw, rfl⟩
        have hbx : b (f * w) * (f * w)⁻¹ = b w * w⁻¹ := by
          rw [map_mul, hf b hb]
          calc f * b w * (f * w)⁻¹ = (f * f⁻¹) * (b w * w⁻¹) := by
                rw [mul_inv_rev]; ac_rfl
            _ = b w * w⁻¹ := by rw [mul_inv_cancel, one_mul]
        have hbxa : b (f * w) * (f * w)⁻¹ ∈ commV a :=
          Subgroup.mul_mem _ (restr_mem_commV hother hstab hbY haI hx2)
            (Subgroup.inv_mem _ hx2)
        have hW1 : b w * w⁻¹ ∈ W := Subgroup.mul_mem _ hbW (Subgroup.inv_mem _ hw)
        have hmem : b w * w⁻¹ ∈ commV a ⊓ ⨆ H' ∈ I, ⨆ (_ : H' ≠ a), commV H' := by
          refine ⟨hbx ▸ hbxa, ?_⟩
          have hle : W ≤ ⨆ H' ∈ I, ⨆ (_ : H' ≠ a), commV H' := by
            refine iSup₂_le fun H hH => ?_
            exact le_iSup₂_of_le (f := fun H' (_ : H' ∈ I) => ⨆ (_ : H' ≠ a), commV H') H
              (hsI hH) (le_iSup_of_le (fun e => ha (e ▸ hH)) le_rfl)
          exact hle hW1
        rw [hind0 a haI, Subgroup.mem_bot] at hmem
        have : b (f * w) = f * w := by
          have h1 : b (f * w) * (f * w)⁻¹ = 1 := by rw [hbx, hmem]
          exact mul_inv_eq_one.1 h1
        exact this
      have e1 := B2F.card_sup_mul_card_inf_of_commute (A := F ⊔ W) (B := commV a)
        (fun x _ y _ => mul_comm x y)
      rw [hinf] at e1
      have e2 : F ⊔ ⨆ H ∈ insert a s, commV H = (F ⊔ W) ⊔ commV a := by
        rw [Finset.iSup_insert, hW]
        calc F ⊔ (commV a ⊔ ⨆ H ∈ s, commV H) = F ⊔ ((⨆ H ∈ s, commV H) ⊔ commV a) := by
              rw [sup_comm (commV a)]
          _ = (F ⊔ ⨆ H ∈ s, commV H) ⊔ commV a := (sup_assoc _ _ _).symm
      rw [e2, Finset.prod_insert ha, Finset.prod_insert ha]
      calc Nat.card ↥((F ⊔ W) ⊔ commV a) * (Nat.card ↥(commV a ⊓ F) *
            ∏ H ∈ s, Nat.card ↥(commV H ⊓ F)) =
          (Nat.card ↥((F ⊔ W) ⊔ commV a) * Nat.card ↥(commV a ⊓ F)) *
            ∏ H ∈ s, Nat.card ↥(commV H ⊓ F) := by ring
        _ = (Nat.card ↥(F ⊔ W) * Nat.card ↥(commV a)) * ∏ H ∈ s, Nat.card ↥(commV H ⊓ F) := by
            rw [e1]
        _ = Nat.card ↥(commV a) * (Nat.card ↥(F ⊔ W) * ∏ H ∈ s, Nat.card ↥(commV H ⊓ F)) := by
            ring
        _ = Nat.card ↥(commV a) * (Nat.card ↥F * ∏ H ∈ s, Nat.card ↥(commV H)) := by rw [ih']
        _ = Nat.card ↥F * (Nat.card ↥(commV a) * ∏ H ∈ s, Nat.card ↥(commV H)) := by ring
  have htop : F ⊔ ⨆ H ∈ I, commV H = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, c, hc, rfl⟩ := hsplit v
    have h1 : w ∈ F ⊔ ⨆ H ∈ I, commV H := Subgroup.mem_sup_right hw
    have h2 : c ∈ F ⊔ ⨆ H ∈ I, commV H := Subgroup.mem_sup_left (hCF hc)
    exact Subgroup.mul_mem _ h1 h2
  have := key I subset_rfl
  rw [htop, Subgroup.card_top] at this
  exact this

end Comp

end GE23

end CFSG.Quasithin
