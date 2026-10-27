module

public section

namespace CFSG.Monster.B.Fischer

@[expose] def fi22FormsText : String :=
  include_str "../../../../Certificates/Data/CFSGNative/Fi22Pinned/fi22-forms.txt"

@[expose] def fi22InvFormText : String :=
  include_str "../../../../Certificates/Data/CFSGNative/Fi22Pinned/fi22-invariant-form.txt"

@[expose] def fi22FormsBytes : ByteArray := fi22FormsText.toUTF8

@[expose] def fi22InvFormBytes : ByteArray := fi22InvFormText.toUTF8

end CFSG.Monster.B.Fischer
